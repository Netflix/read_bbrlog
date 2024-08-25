#include <sys/types.h>
#include <sys/callout.h>
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <unistd.h>
#include <string.h>
#include <strings.h>
#include <sys/errno.h>
#include <sys/param.h>
#include <sys/mbuf.h>
#include <sys/sysctl.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/tree.h>
#include <sys/tim_filter.h>
#include <sys/osd.h>
#include <getopt.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <arpa/inet.h>
#define	_WANT_INPCB
#include <netinet/in_pcb.h>
#include <netinet/tcp_hpts.h>
#include <dev/tcp_log/tcp_log_dev.h>
#include <netinet/tcp_log_buf.h>
#include <netinet/tcp_seq.h>
#define	_WANT_TCPCB
#include <netinet/tcp_var.h>
#include <netinet/tcp_hpts.h>
#include <netinet/tcp_stacks/sack_filter.h>
#include <netinet/tcp_stacks/tcp_bbr.h>
#include <netinet/tcp_stacks/tcp_rack.h>
#include <netinet/tcp_stacks/rack_bbr_common.h>
#include <net/route.h>

#include <assert.h>

static const char *prurequests[] = {
	"ATTACH",	"DETACH",	"BIND",		"LISTEN",
	"CONNECT",	"ACCEPT",	"DISCONNECT",	"SHUTDOWN",
	"RCVD",		"SEND",		"ABORT",	"CONTROL",
	"SENSE",	"RCVOOB",	"SENDOOB",	"SOCKADDR",
	"PEERADDR",	"CONNECT2",	"FASTTIMO",	"SLOWTIMO",
	"PROTORCV",	"PROTOSEND",	"SEND_EOF",	"SOSETLABEL",
	"CLOSE",	"FLUSH",
};

#include <bbparse.h>

#define	tcp_get_flags(th)		__tcp_get_flags(th)
#define	tcp_set_flags(th, flags)	__tcp_set_flags(th, flags)

static uint32_t lowest_delta = 0xffffffff;
static uint32_t highest_delta = 0;
static int32_t showExtraInfo = 0;
static int32_t file_count_limit = 0;
static int32_t file_count_at = 0;
static int32_t use_relative_seq = 0;
static int32_t change_tracking = 0;
static void
print_pace_size(const struct tcp_log_buffer *, const struct tcp_log_bbr *);

static FILE *dump_out_sack=NULL;
#define	MAX_TYPES  TCP_LOG_END
static int extra_print = 0;
static int number_flow = 0;
static uint32_t record_num_start = 0;
static uint32_t record_num_end = 0;
static uint8_t num_start_set = 0;
static uint8_t num_end_set = 0;
static uint8_t tag_dumped = 0;
static char log_tag[TCP_LOG_TAG_LEN];
static uint32_t time_in_hot = 0;

static int print_out_the_time = 0;
static int show_all_messages=1;
static uint32_t out_count = 0;
static int display_file_names = 0;
static uint32_t warn_behind=0;

static int irs = 0;
static int irs_set = 0;

static const char *dirname = NULL;
static uint32_t epoch_lost = 0;
static uint32_t epoch_delivered = 0;
static uint32_t first_time=0;
static int first_time_set=0;
static int bbr_first_time_set=0;
static int time_is_relative = 0;
static const struct tcp_log_header *lh = NULL;
static int display_wallclock_time = 0;
static int use_monolithic_time = 0;
static uint32_t prev_sent_bytes = 0;
static uint32_t prev_sn = 0;
static uint64_t prev_sent_time = 0;
static int clear_to_print = 1;

/*#define BBR_RED_BW_CONGSIG  	 0	 We enter recovery and set using b/w */
/*#define BBR_RED_BW_RATECAL  	 1	 We are calculating the loss rate */
/*#define BBR_RED_BW_USELRBW       2	 We are dropping the lower b/w with cDR*/
/*#define BBR_RED_BW_SETHIGHLOSS   3	 We have set our highloss value at exit from probe-rtt */
/*#define BBR_RED_BW_PE_CLREARLY    4	 We have decided to clear the reduction early */
/*#define BBR_RED_BW_PE_CLAFDEL	 5	 We are clearing it on schedule delayed */
/*#define BBR_RED_BW_REC_ENDCLL	 6	 Recover exits save high if needed an clear to start measuring */
/*#define BBR_RED_BW_PE_NOEARLY_OUT 7	 Set pkt epoch judged that we do not get out of jail early */


static const char *tcp_accounting_names[] = {
	"ACK_BEHIND",
	"ACK_SACK",
	"ACK_CUMACK",
	"ACK_CUMACK_SACK",
	"ACK_DUPACK",
	"ACK_RWND",
	"SND_BLOCKED",
	"SND_LIMITED",
	"SND_OUT_DATA",
	"SND_OUT_ACK",
	"SND_OUT_FAIL",
	"CNT_OF_MSS_OUT",
	"CNT_OF_ACKS_IN"
};

static const char *tcp_cycle_names[] = {
	"ACK_BEHIND",
	"ACK_SACK",
	"ACK_CUMACK",
	"ACK_CUMACK_SACK",
	"ACK_DUPACK",
	"ACK_RWND",
	"SND_BLOCKED",
	"SND_LIMITED",
	"SND_OUT_DATA",
	"SND_OUT_ACK",
	"SND_OUT_FAIL",
	"CYC_HANDLE_MAP",
	"CYC_HANDLE_ACK"
};

static const char *map_chg_names[] = {
	"None",
	"Merge",
	"Split",
	"New",
	"SACK_M1",
	"SACK_M2",
	"SACK_M3",
	"SACK_M4",
	"SACK_M5",
	"Free",
	"Trim Head",
	"None"
};



#define MAX_RED_BW_REASONS 9
static const char *red_bw_reasons[MAX_RED_BW_REASONS] = {
	"Recovery Begins",
	"Calculate loss rate",
	"Adopt lower red b/w",
	"ProbeRTT sets new threshold",
	"Clear reduction early",
	"Clear reduction on sched",
	"Exiting recovery",
	"No early out",
	"Unknown"
};

#define PACE_TMR_DELACK 0x01	/* Delayed ack timer running */
#define PACE_TMR_RACK   0x02	/* RACK timer running */
#define PACE_TMR_TLP    0x04	/* TLP timer running */
#define PACE_TMR_RXT    0x08	/* Retransmit timer running */
#define PACE_TMR_PERSIT 0x10	/* Persists timer running */
#define PACE_TMR_KEEP   0x20	/* Keep alive timer running */
#define PACE_PKT_OUTPUT 0x40	/* Output Packets being paced */
#define PACE_TMR_MASK   (PACE_TMR_KEEP|PACE_TMR_PERSIT|PACE_TMR_RXT|PACE_TMR_TLP|PACE_TMR_RACK|PACE_TMR_DELACK)

static uint64_t under_256 = 0;
static uint64_t over_256 = 0;
static uint64_t at_256 = 0;
static uint64_t under_drain = 0;
static uint64_t under_rtt = 0;
static uint64_t under_subdr = 0;

static uint64_t time_in_state[3];
#define STATE_SS 0
#define STATE_CA 1
#define STATE_REC 2
static uint32_t time_entered = 0;
static int32_t gp_state = 0;
static void
add_time_to_state(uint32_t now, int new_state)
{
	if (TSTMP_GT(now, time_entered))
	    time_in_state[gp_state] += (now - time_entered);
	gp_state = new_state;
	time_entered = now;
}

static void inline
print_out_space(FILE *outp)
{
	fprintf(outp, "                             ");
}

static struct timeval earliest_time;
static struct timeval connection_begin_time;
static struct timeval last_time;
static int early_filled = 0;

static uint64_t msg_types_list[MAX_TYPES];
static uint16_t last_major_state = 0;
static uint16_t last_minor_state = 0;
static uint64_t total_missed_records = 0;
static const char *log_names[MAX_TYPES] = {
	"UNKNOWN           ",
	"IN        ", /* Incoming packet                 1 */
	"PKT_OUT   ", /* Transmit (without other event)  2 */
	"RTO       ", /* Retransmit timeout              3 */
	"SOWAKE    ", /* We wokeup a socket buffer       4 */
	"TCP_UNUSED_5", /* Detected bad retransmission   5 */
	"PRR       ", /* Doing PRR                       6 */
	"REORDER   ", /* Detected reorder                7 */
	"PACER     ", /* Pacer sending a packet          8 */
	"BBRUPD    ", /* We updated BBR info     9 */
	"BBRSND    ", /* We did a slot calculation and sending is done 10 */
	"ACKCLEAR  ", /* A ack clears all outstanding     11 */
	"INQUEUE   ", /* The tcb had a packet input to it 12 */
	"TIMERSTAR ", /* Start a timer                    13 */
	"TIMERCANC ", /* Cancel a timer                   14 */
	"ENTREC    ", /* Entered recovery                 15 */
	"EXITREC   ", /* Exited recovery                  16 */
	"LOG_CWND  ", /* Cwnd change                      17 */
	"BWSAMP    ", /* LT B/W sample has been made      18 */
	"MSGSIZE   ", /* We received a EMSGSIZE error     19 */
	"BBRRTT    ", /* BBR RTT is updated               20 */
	"JUSTRET   ", /* We just returned out of output   21 */
	"STATE     ", /* A BBR state change occured       22 */
	"PKT_EPOCH ", /* A packet epoch occured           23 */
	"PERSIST   ", /* We enter/exit persists           24 */
	"FLOWEND   ", /* end of a flow                    25 */
	"RTO       ", /* a BBR timeout mark               26 */
	"DOSEG_DONE", /* End of pacer do segment          27 */
	"EXIT_GAIN ", /* pacer do_segment completes       28 */
	"THRESH_CALC",/* log the calculation routine      29 */
	"MAP_CHGS",   /* Map changes to the sendmap       30 */
	"USERSEND  ", /* User level sends data            31 */
	"RSM_CLEAR ", /* Unused                           32 */
	"STATE_TARGET", /* Set of state target              33 */
	"EPOCH_TIME", /* A timed based Epoch occured      34 */
	"LOG_TO_PRO", /* A to was processed               35 */
	"TSO_SZ_UPD", /* Update the TSO size              36 */
	"PACERDIAG ", /* A pacer diag msg                 37 */
	"RWND COMP ", /* Log a low gain event             38 */
	"PROGRESS  ", /* A progress event		  39 */
	"TCP_OPTION", /* A tcp option is set		  40 */
	"BBR_LOG_TIMERPREP", /* timing calc check         41 */
	"BBR_ENOBUF_JMP",	/* 42 */
	"BBR_PACING_CALC",	/* 43 */
	"BBR_RTT_SHRINKS",	/* 44 */
	"BBR_LOG_BW_RED_EV",     /* 45 */
	"BBR_STARTUP_LOG",     /* 46 */
	"TCP_LOG_RTT",	       /* 47 */
	"BBR_SETTINGS",		/* 48 */
	"TCP_UNUSED_49",	/* 49 */
	"TCP_LOG_REASS", 	/* 50 */
 	"TCP_PACE_SIZE",	/* 51 */
	"BBR_TCP_HDWR_PACE",	/* 52 */
	"BBR_LOG_TSTMP_VAL",	/* 53 */
	"TCP_LOG_CONNEND", 	/* 54 */
	"TCP_LRO_LOG",		/* 55 */
	"SACK_FILTER_RESULT",	/* 56 */
	"TCP_UNUSED_57",	/* 57 */
	"TCP_TIMELY_WORK",	/* 58 */
	"TCP_UNUSED_59",	/* 59 */
	"SENDFILE  ",		/* 60 */
	"TCP_LOG_REQ_T",	/* 61 */
	"TCP_ACCOUNTING",	/* 62 */
	"TCP_LOG_FSB", 		/* 63 */
	"RACK_DSACK_HANDLING",  /* 64 */
	"TCP_HYSTART", 		/* 65 */
	"TCP_CHG_QUERY",	/* 66 */
	"TCP_RACK_LOG_COLLAPSE", /* 67 */
	"RACK_TP_TRIGGERED",	/* 68 */
	"TCP_HYBRID_PACING",	/* 69 */
	"TCP_LOG_PRU",		/* 70 */
};

static uint32_t time_last_setting = 0;
static int last_set_set=0;

static uint32_t last_ack_time = 0;
static uint32_t last_spa_seen = 0;
static uint32_t last_out_time = 0;
static uint32_t last_input_time = 0;
static uint32_t last_pg_chg=0;
static uint32_t opg=0;
static uint32_t last_evt_time=0;
static uint64_t time_avail_zero = 0;
static uint32_t time_saw_avail_zero = 0;
static uint32_t avail_is_zero = 1;
static uint32_t saw_ltbw_set = 0;

#define REASON_MAX 10
static const char *lt_bw_reasons[REASON_MAX] = {
	"Stop using lt bw", 		/* 0 */
	"Begin sampling lt bw",		/* 1 */
	"App Limit reset sample",	/* 2 */
	"Been too long reset sampling", /* 3 */
	"Being Policed use lt bw",	/* 4 */
	"Saved a lt bw sample",		/* 5 */
	"Not enough time or loss",	/* 6 */
	"False detection negative",	/* 7 */
	"False detection postive",	/* 8 */
	"Unknown"			/* 9 */
};

static FILE *out = NULL;
#include <netinet/tcp_stacks/sack_filter.h>
#include <netinet/tcp_stacks/tcp_bbr.h>

static const char *
evt_name(int id)
{

	if (id < 0 || id >= MAX_TYPES) {
		static char log_name_foo[65];
		sprintf(log_name_foo, "Unknown:%d",
			id);
		return(log_name_foo);
	}
	return(log_names[id]);
}



static char *
display_bw(uint64_t bw, int uniq_cpy)
{
	static char human_bw[256];
	double bw_d;
	bw_d = bw * 8.0;
	if (bw_d >= 1000000000.0) {
		sprintf(human_bw, "%.2f Gbps", (bw_d/1000000000.0));
	} else if (bw_d >= 1000000.0) {
		sprintf(human_bw, "%.2f Mbps", (bw_d/1000000.0));
	} else if (bw_d >= 1000.0) {
		sprintf(human_bw, "%.2f kbps", (bw_d/1000.0));
	} else {
		sprintf(human_bw, "%.2f bps", bw_d);
	}
	if (uniq_cpy) {
		char *cp;
		cp = malloc(256);
		strcpy(cp, human_bw);
		return(cp);
	} else {
		return(human_bw);
	}
}

static void
display_tcp_rto(const struct tcp_log_buffer *l)
{
	int what;
	int which;
	const char *timer_types[] = {
		"TT_REXMT",
		"TT_PERSIST",
		"TT_KEEP",
		"TT_2MSL",
		"TT_DELACK",
		"TT_N"
	};
	const char *timer_events[]  = {
		"TT_PROCESSING",
		"TT_PROCESSED",
		"TT_STARTING",
		"TT_STOPPING",
		"TT_UNK"
	};
	what = (l->tlb_flex1 >> 8);
	which = (l->tlb_flex1 & 0xff);
	if (which > 5)
		which = 5;
	if (what > 4)
		what = 4;
	fprintf(out, "Type:%s Event:%s\n",
		timer_types[which],
		timer_events[what]);
}

static int cg_tk_filled = 0;
static struct tcp_log_buffer last_buffer;

static const char *
show_diff(uint32_t old, uint32_t new)
{
	static char print_buffer[100];
	uint32_t delta;
	
	if (old > new) {
		delta = old - new;
		sprintf(print_buffer, "(-%u)",
			delta);
	} else {
		delta = new - old;
		sprintf(print_buffer, "(+%u)",
			delta);
	}
	return ((const char *)print_buffer);
}

static void
change_tracking_check(const struct tcp_log_buffer *l)
{
	if (cg_tk_filled == 0) {
		cg_tk_filled = 1;
		memcpy(&last_buffer, l, sizeof(struct tcp_log_buffer));
		return;
	}
	/* Check and display any changes in the current log vs the previous */
	if (last_buffer.tlb_stackid != l->tlb_stackid) {
		print_out_space(out);
		fprintf(out, "CHG tlb_stackid OLD:%u NEW:%u\n",
			last_buffer.tlb_stackid,l->tlb_stackid);
	}
	if (last_buffer.tlb_state != l->tlb_state) {
		print_out_space(out);
		fprintf(out, "CHG tlb_state OLD:%u NEW:%u\n",
			last_buffer.tlb_state, l->tlb_state);
	}
	if (last_buffer.tlb_flags != l->tlb_flags) {
		print_out_space(out);
		fprintf(out, "CHG tlb_flags OLD:0x%x NEW:0x%x\n",
			last_buffer.tlb_flags, l->tlb_flags);
	}
	if (last_buffer.tlb_snd_una != l->tlb_snd_una) {
		print_out_space(out);
		fprintf(out, "CHG tlb_snd_una OLD:%u NEW:%u %s\n",
			last_buffer.tlb_snd_una, l->tlb_snd_una,
			show_diff(last_buffer.tlb_snd_una, l->tlb_snd_una));
	}
	if (last_buffer.tlb_snd_max != l->tlb_snd_max) {
		print_out_space(out);
		fprintf(out, "CHG tlb_snd_max OLD:%u NEW:%u %s\n",
			last_buffer.tlb_snd_max, l->tlb_snd_max,
			show_diff(last_buffer.tlb_snd_max, l->tlb_snd_max));
	}
	if (last_buffer.tlb_snd_cwnd != l->tlb_snd_cwnd) {
		print_out_space(out);
		fprintf(out, "CHG tlb_snd_cwnd OLD:%u NEW:%u %s\n",
			last_buffer.tlb_snd_cwnd, l->tlb_snd_cwnd,
			show_diff(last_buffer.tlb_snd_cwnd, l->tlb_snd_cwnd));
	}
	if (last_buffer.tlb_snd_nxt != l->tlb_snd_nxt) {
		print_out_space(out);
		fprintf(out, "CHG tlb_snd_nxt OLD:%u NEW:%u %s\n",
			last_buffer.tlb_snd_nxt, l->tlb_snd_nxt,
			show_diff(last_buffer.tlb_snd_nxt, l->tlb_snd_nxt));
	}
	if (last_buffer.tlb_snd_recover != l->tlb_snd_recover) {
		print_out_space(out);
		fprintf(out, "CHG tlb_snd_recover OLD:%u NEW:%u %s\n",
			last_buffer.tlb_snd_recover, l->tlb_snd_recover,
			show_diff(last_buffer.tlb_snd_recover, l->tlb_snd_recover));
	}
	if (last_buffer.tlb_snd_wnd != l->tlb_snd_wnd) {
		print_out_space(out);
		fprintf(out, "CHG tlb_snd_wnd OLD:%u NEW:%u %s\n",
			last_buffer.tlb_snd_wnd, l->tlb_snd_wnd,
			show_diff(last_buffer.tlb_snd_wnd, l->tlb_snd_wnd));
	}
	if (last_buffer.tlb_snd_ssthresh != l->tlb_snd_ssthresh) {
		print_out_space(out);
		fprintf(out, "CHG tlb_snd_ssthresh OLD:%u NEW:%u %s\n",
			last_buffer.tlb_snd_ssthresh, l->tlb_snd_ssthresh,
			show_diff(last_buffer.tlb_snd_ssthresh, l->tlb_snd_ssthresh));
	}
	if (last_buffer.tlb_srtt != l->tlb_srtt) {
		print_out_space(out);
		fprintf(out, "CHG tlb_srtt OLD:%u NEW:%u %s\n",
			last_buffer.tlb_srtt, l->tlb_srtt,
			show_diff(last_buffer.tlb_srtt, l->tlb_srtt));
	}
	if (last_buffer.tlb_rttvar != l->tlb_rttvar) {
		print_out_space(out);
		fprintf(out, "CHG tlb_rttvar OLD:%u NEW:%u %s\n",
			last_buffer.tlb_rttvar, l->tlb_rttvar,
			show_diff(last_buffer.tlb_rttvar, l->tlb_rttvar));
	}
	if (last_buffer.tlb_rcv_up != l->tlb_rcv_up) {
		print_out_space(out);
		fprintf(out, "CHG tlb_rcv_up OLD:%u NEW:%u\n",
			last_buffer.tlb_rcv_up, l->tlb_rcv_up);
	}
	if (last_buffer.tlb_rcv_adv != l->tlb_rcv_adv) {
		print_out_space(out);
		fprintf(out, "CHG tlb_rcv_adv OLD:%u NEW:%u %s\n",
			last_buffer.tlb_rcv_adv, l->tlb_rcv_adv,
			show_diff(last_buffer.tlb_rcv_adv, l->tlb_rcv_adv));
	}
	if (last_buffer.tlb_flags2 != l->tlb_flags2) {
		print_out_space(out);
		fprintf(out, "CHG tlb_flags2 OLD:0x%x NEW:0x%x\n",
			last_buffer.tlb_flags2, l->tlb_flags2);
	}
	if (last_buffer.tlb_rcv_nxt != l->tlb_rcv_nxt) {
		print_out_space(out);
		fprintf(out, "CHG tlb_rcv_nxt OLD:%u NEW:%u %s\n",
			last_buffer.tlb_rcv_nxt, l->tlb_rcv_nxt,
			show_diff(last_buffer.tlb_rcv_nxt, l->tlb_rcv_nxt));
	}
	if (last_buffer.tlb_rcv_wnd != l->tlb_rcv_wnd) {
		print_out_space(out);
		fprintf(out, "CHG tlb_rcv_wnd OLD:%u NEW:%u %s\n",
			last_buffer.tlb_rcv_wnd, l->tlb_rcv_wnd,
			show_diff(last_buffer.tlb_rcv_wnd, l->tlb_rcv_wnd));
	}
	if (last_buffer.tlb_dupacks != l->tlb_dupacks) {
		print_out_space(out);
		fprintf(out, "CHG tlb_dupacks OLD:%u NEW:%u %s\n",
			last_buffer.tlb_dupacks, l->tlb_dupacks,
			show_diff(last_buffer.tlb_dupacks, l->tlb_dupacks));
	}
	if (last_buffer.tlb_segqlen != l->tlb_segqlen) {
		print_out_space(out);
		fprintf(out, "CHG tlb_segqlen OLD:%u NEW:%u %s\n",
			last_buffer.tlb_segqlen, l->tlb_segqlen,
			show_diff(last_buffer.tlb_segqlen, l->tlb_segqlen));
	}
	if (last_buffer.tlb_snd_numholes != l->tlb_snd_numholes) {
		print_out_space(out);
		fprintf(out, "CHG tlb_snd_numholes OLD:%u NEW:%u\n",
			last_buffer.tlb_snd_numholes, l->tlb_snd_numholes);
	}
	if (last_buffer.tlb_snd_scale != l->tlb_snd_scale) {
		print_out_space(out);
		fprintf(out, "CHG tlb_snd_scale OLD:%u NEW:%u\n",
			last_buffer.tlb_snd_scale,  l->tlb_snd_scale);
	}
	if (last_buffer.tlb_rcv_scale != l->tlb_rcv_scale) {
		print_out_space(out);
		fprintf(out, "CHG tlb_rcv_scale OLD:%u NEW:%u\n",
			last_buffer.tlb_rcv_scale, l->tlb_rcv_scale);
	}
	memcpy(&last_buffer, l, sizeof(struct tcp_log_buffer));

}


static char *
get_timer_mask(uint32_t tmask)
{
	static char mask_value[256];
	int outr=0;

	memset(mask_value, 0, sizeof(mask_value));
	if (tmask & PACE_TMR_DELACK) {
		strcat(mask_value, "DACK");
		outr = 1;
	} else 	if (tmask & PACE_TMR_RACK) {
		strcat(mask_value, "RACK");
		outr = 1;
	} else 	if (tmask & PACE_TMR_TLP) {
		strcat(mask_value, "TLP");
		outr = 1;
	} else if (tmask & PACE_TMR_RXT) {
		strcat(mask_value, "RXT");
		outr = 1;
	} else if (tmask & PACE_TMR_PERSIT) {
		strcat(mask_value, "PER");
		outr = 1;
	} else if (tmask & PACE_TMR_KEEP) {
		strcat(mask_value, "KEEP");
		outr = 1;
	}
	if (tmask & PACE_PKT_OUTPUT) {
		if (outr)
			strcat(mask_value, " & OUTPUT");
		else
			strcat(mask_value, "OUTPUT");
		outr++;
	}
	if (outr == 0)
		strcat(mask_value, "NONE");
	return(mask_value);
}


static char *
translate_flags(uint16_t flags)
{
	static char flagbuf[256];
	memset(flagbuf, 0, sizeof(flagbuf));
	int buf_at = 0;

	if (flags & TH_FIN) {
		strcat(flagbuf, "FIN");
		buf_at += 3;
	}
	if (flags & TH_SYN) {
		if (buf_at)
			strcat(flagbuf, "|");
		strcat(flagbuf, "SYN");
		buf_at += 3;
	}
	if (flags & TH_RST) {
		if (buf_at)
			strcat(flagbuf, "|");
		strcat(flagbuf, "RST");
		buf_at += 3;
	}
	if (flags & TH_PUSH) {
		if (buf_at)
			strcat(flagbuf, "|");
		strcat(flagbuf, "PUS");
		buf_at += 3;
	}
	if (flags & TH_ACK) {
		if (buf_at)
			strcat(flagbuf, "|");
		strcat(flagbuf, "ACK");
		buf_at += 3;
	}
	if (flags & TH_URG) {
		if (buf_at)
			strcat(flagbuf, "|");
		strcat(flagbuf, "URG");
		buf_at += 3;
	}
	if (flags & TH_ECE) {
		if (buf_at)
			strcat(flagbuf, "|");
		strcat(flagbuf, "ECE");
		buf_at += 3;
	}
	if (flags & TH_CWR) {
		if (buf_at)
			strcat(flagbuf, "|");
		strcat(flagbuf, "CWR");
		buf_at += 3;
	}
	if (flags & TH_AE) {
		if (buf_at)
			strcat(flagbuf, "|");
		strcat(flagbuf, "AE");
		buf_at += 2;
	}
	if (buf_at == 0)
		strcat(flagbuf, "NON");
	return(flagbuf);
}

static uint64_t
bbr_get_bw_delay_prod(uint64_t rtt, uint64_t bw)
{
	/*
	 * Calculate the bytes in flight needed give the bw (in bytes per
	 * second) and the specifyed rtt in useconds. We need to put out the
	 * returned value per RTT to match that rate. Gain will normaly
	 * raise it up from there.
	 */
	uint64_t usec_per_sec, bdp;

	usec_per_sec = 1000000;
	bdp = (rtt * bw)/usec_per_sec;
	return (bdp);
}

static uint32_t
bbr_get_target_cwnd(uint64_t bw, uint64_t rtt, uint32_t gain)
{
	uint64_t bdp;
	uint32_t cwnd;
#ifdef DO_ROUND
	uint32_t mss, even_targ;
#endif
	/* Get the bdp from the two values */
	bdp = bbr_get_bw_delay_prod(rtt, bw);

	/* Now apply the gain */
	cwnd = (uint32_t) (((bdp * ((uint64_t) gain)) + (uint64_t) (BBR_UNIT - 1)) / ((uint64_t) BBR_UNIT));
	/* round up to then next mss boundary  */
#ifdef DO_ROUND
	mss = (bbr->rc_tp->t_maxseg - bbr->r_ctl.rc_last_options);
	even_targ = (cwnd + (mss - 1)) / mss;
	/* Lets make sure its an even number */
	if (even_targ & 0x01) {
		even_targ++;
	}
	cwnd = even_targ * mss;
#endif
	return (cwnd);
}


static const char *timer_types[7] = {
	"UNKN",
	"RTO ",
	"TLP ",
	"RACK",
	"KEEP",
	"PERS",
	"DACK"
};

#define BBR_TO_FRM_TMR  1
#define BBR_TO_FRM_TLP  2
#define BBR_TO_FRM_RACK 3

static const char *major_state[6] = {
	"UNKNOWN STATE",
	"BBR_STATE_STARTUP",
	"BBR_STATE_DRAIN",
	"BBR_STATE_PROBE_BW",
	"BBR_STATE_PROBE_RTT",
	"BBR_STATE_PERSIST_EXIT",
};

static const char *startup_reasons[12] = {
	"Back from probe-rtt", 	/* 0 */
	"Not up to speed", /* 1 */
	"No loss at target", /* 2 */
	"Had large Gain", /* 3 */
	"Loss forces exit", /* 4 */
	"Record new loss", /* 5 */
	"Exit to drain", /* 6 */
	"Not enough measurements", /* 7 */
	"No exit required", /* 8 */
	"No measurements", /* 9 */
	"No loss no inc-rtt", /* 10 */
	"No loss so stay" /* 11 */
};

/*
 * startup = 10
 * drain   = 20
 * probe_rtt = 30
 * probe_bw = 40 - 110.
 */
static const char *
state_at_to_state_name(uint32_t st)
{
	switch (st) {
	case 10:
		return ("STARTUP");
	case 20:
		return ("DRAIN");
	case 30:
		return ("PROBE_RTT");
	case 40:
		return ("PROBE_BW GAIN");
	case 50:
		return ("PROBE_BW DRAIN");
	case 60:
		return ("PROBE_BW LEVEL1");
	case 70:
		return ("PROBE_BW LEVEL2");
	case 80:
		return ("PROBE_BW LEVEL3");
	case 90:
		return ("PROBE_BW LEVEL4");
	case 100:
		return ("PROBE_BW LEVEL5");
	case 110:
		return ("PROBE_BW LEVEL6");
	default:
		return ("UNKNOWN");
	}
}

static const char *
get_progress_event(uint8_t id)
{
	static char foobar[64];
	const char *ret;
	if (id == 1) {
		ret = "Dropping conn    ";
	} else if (id == 2) {
		ret = "Updating ticks   ";
	} else if (id == 3) {
		ret = "Stop una = th_ack";
	} else if (id == 4) {
		ret = "Starting una  inc";
	} else {
		sprintf(foobar, "Unknown:%d", id);
		ret = foobar;
	}
	return(ret);
}


static int
pad_out(int at, int to)
{
	int i, cnt=0;

	for(i=at; i<to; i++) {
		cnt += fprintf(out, " ");
	}
	return(cnt);
}

static uint32_t state_at = 10;

static uint32_t tlb_sn = 0;
static uint32_t tlb_sn_set = 0;
static uint32_t duplicates=0;
static int old_state = 0;
static uint32_t epoch=0;
static uint32_t epoch_time=0;
static uint64_t del_rate=0;
static uint32_t prev_pkt_epoch=0;
static uint64_t pe_btlbw=0;
static int pg_not_set=1;
static int log_all_state_change = 1;


static uint64_t sent_state[9];
static uint64_t retran_count=0;

static uint32_t time_started_using_ltbw=0;

static int using_lt_bw=0;
static uint64_t total_time_using_lt_bw=0;

static uint64_t total_time_in_trace=0;
static uint32_t last_time_stamp;

static uint64_t total_time_persisting=0;
static uint64_t total_time_app_limited=0;
static uint32_t timeOfAppLimit;
static int is_app_limited=0;
static uint64_t app_limited_transitions=0;

static uint64_t total_time_no_avail=0;
static uint32_t timeOfnoAvail;
static int is_none_avail;

static uint64_t total_time_ltbw_sendok;
static int is_ltbw_sndok=0;
static uint32_t time_data_ltbw;

static uint64_t total_time_no_rwnd=0;
static uint32_t timeOfnoRwnd;
static uint32_t time_ended_using_lt_bw=0;
static int is_none_rwnd;

static uint32_t delivered_at_thresh=0;
static uint32_t lost_at_thresh=0;
static uint32_t policing_on = 0;
static int set_pkt_epoch = 0;

static uint32_t del_at_state=0;
static uint32_t lost_at_state=0;
static uint32_t state_send_count = 0;
static uint32_t state_send_bytes = 0;

static uint32_t max_rtt_in_state = 0;
static uint32_t min_rtt_in_state = 0xffffffff;

#define NUM_PKT_EPOCH_TRK 8
static int32_t pkt_epoch_lost[NUM_PKT_EPOCH_TRK];
static int32_t pkt_epoch_del[NUM_PKT_EPOCH_TRK];
static int32_t num_pkt_ep_filled=0;


static void
display_map_chg(const struct tcp_log_bbr *bbr)
{
	if (bbr->flex8 > 11) {
		fprintf(out, "Found %u at mapchg?\n",
			bbr->flex8);
			return;
	}
	fprintf(out, " - %s line:%d ",
		map_chg_names[bbr->flex8], bbr->applimited);
	if (bbr->flex7 & 0x4) {
		fprintf(out, "pr_s:%u pr_e:%u (%u) ",
			bbr->flex1, bbr->flex2,
			(bbr->flex2 - bbr->flex1));
	}
	if (bbr->flex7 & 0x2) {
		fprintf(out, "at_s:%u at_e:%u (%u) ",
			bbr->flex3, bbr->flex4,
			(bbr->flex4 - bbr->flex3));
	}
	if (bbr->flex7 & 0x1) {
		fprintf(out, "nx_s:%u nx_e:%u (%u) ",
			bbr->flex5, bbr->flex6,
			(bbr->flex6 - bbr->flex5));
	}
	fprintf(out, " end:%u\n", bbr->pkts_out);
	if (extra_print) {
		print_out_space(out);
		fprintf(out, "prev:0x%lx rsm:0x%lx next:0x%lx\n",
			bbr->cur_del_rate,
			bbr->delRate,
			bbr->rttProp);
	}
}

static void
pkt_epoch_track(uint32_t pe, uint32_t lost, uint32_t del)
{
	int idx, i;
	if (num_pkt_ep_filled >= NUM_PKT_EPOCH_TRK)
		idx = NUM_PKT_EPOCH_TRK - 1;
	else
		idx = (pe - 1) % NUM_PKT_EPOCH_TRK;
	for(i=idx; i>0; i--) {
		pkt_epoch_del[i] = pkt_epoch_del[(i-1)];
		pkt_epoch_lost[i] = pkt_epoch_lost[(i-1)];
	}
	pkt_epoch_del[0] = del;
	pkt_epoch_lost[0] = lost;
	if (num_pkt_ep_filled < NUM_PKT_EPOCH_TRK)
		num_pkt_ep_filled++;
}

static void
print_epoch_loss(uint32_t pe, uint32_t lost, uint32_t del)
{
	int i;
	double r, l, d;

	l = (100.0 * lost);
	d = (1.0 * del);
	if (l == 0.0) {
		r = 0.0;
	} else if (d == 0.0) {
		r = 100.0;
	} else {
		r = l/d;
	}
	fprintf(out, "LOSS_RATES:(o-a)%2.1f%% ", r);
	for(i=0; i<num_pkt_ep_filled; i++) {
		l = (100.0 * (lost - pkt_epoch_lost[i]));
		d = (1.0 * (del - pkt_epoch_del[i]));
		if (l == 0.0) {
			r = 0.0;
		} else if (d == 0.0) {
			r = 100.0;
		} else {
			r = l/d;
		}
		fprintf(out, "(%d)%2.1f%% ",
			(i+1), r);
	}
	fprintf(out, "\n");
	pkt_epoch_track(pe, lost, del);
}

static void
dump_sack_filter(const struct tcp_log_bbr *bbr)
{
	fprintf(out, "%d entries left\n", bbr->flex8);
	if (bbr->flex8 > 0) {
		print_out_space(out);
		fprintf(out, "SACK:%u:%u (%u)\n",
			bbr->flex1, bbr->flex2,
			(bbr->flex2 - bbr->flex1));
	}
	if (bbr->flex8 > 1) {
		print_out_space(out);
		fprintf(out, "SACK:%u:%u (%u)\n",
			bbr->flex3, bbr->flex4,
			(bbr->flex4 - bbr->flex3));
	}
	if (bbr->flex8 > 2) {
		print_out_space(out);
		fprintf(out, "SACK:%u:%u (%u)\n",
		       bbr->flex5, bbr->flex6,
		       (bbr->flex6 - bbr->flex5));
	}
	if (bbr->flex8 > 3) {
		print_out_space(out);
		fprintf(out, "SACK:%u:%u (%u)\n",
		       bbr->applimited,
		       bbr->pkts_out,
		       (bbr->pkts_out - bbr->applimited));
	}
}

static void
sort_sack_blocks(struct sackblk *sack_blocks, int num_sack_blks)
{
	struct sackblk low;
	int i, sack_pos = 0;

restart:
	memcpy(&low, &sack_blocks[sack_pos], sizeof(struct sackblk));
	for(i = (sack_pos+1); i < num_sack_blks; i++) {
		if (low.start > sack_blocks[i].start) {
			/* this one is lower */
			memcpy(&sack_blocks[sack_pos],
			       &sack_blocks[i],
			       sizeof(struct sackblk));
			memcpy(&sack_blocks[i], &low,
			       sizeof(struct sackblk));
			goto restart;
		}
	}
	if (sack_pos < (num_sack_blks - 1)) {
		/* need to sort the rest */
		sack_pos++;
		goto restart;
	}
}

static int32_t sort_all_sacks = 1;

static void
print_sack_blocks(struct tcpopt *to, uint32_t th_ack)
{
	int i, num_sack_blks=0, low_set = 0;
	tcp_seq lowest;

	struct sackblk sack, sack_blocks[TCP_MAX_SACK + 1];
	if ((to->to_flags & TOF_SACK) == 0)
		/* Nothing to see here folks */
		return;

	memset(sack_blocks, 0, sizeof(sack_blocks));
	for (i = 0; i < to->to_nsacks; i++) {
		bcopy((to->to_sacks + i * TCPOLEN_SACK),
		    &sack, sizeof(sack));
		sack.start = ntohl(sack.start);
		sack.end = ntohl(sack.end);
		sack_blocks[num_sack_blks] = sack;
		num_sack_blks++;
	}
	if (num_sack_blks == 0)
		return;
	if ((num_sack_blks > 1) && sort_all_sacks) {
		/* Lets sort them into order */
		sort_sack_blocks(sack_blocks, num_sack_blks);
	}
	if (dump_out_sack) {
		print_out_space(out);
		fprintf(dump_out_sack, "ACK:%u\n", th_ack);
	}
	print_out_space(out);
	for (i = 0; i < to->to_nsacks; i++) {
		if ((low_set == 0) || (SEQ_LT(sack_blocks[i].start, lowest))) {
			lowest = sack_blocks[i].start;
			low_set = 1;
		}
	}
	if (SEQ_LT(lowest, th_ack))
		fprintf(out, "ACK:%u\n", th_ack);
	else
		fprintf(out, "ACK:%u (missing %u)\n", th_ack, (sack_blocks[0].start - th_ack));
	for(i=0; i<num_sack_blks; i++) {
		print_out_space(out);
		if (SEQ_LT(sack_blocks[i].start, th_ack))
			fprintf(out, "D-SACK:%u:%u (%u)\n",
				sack_blocks[i].start,
				sack_blocks[i].end,
				(sack_blocks[i].end - sack_blocks[i].start));
		else
			fprintf(out, "SACK:%u:%u (%u)\n",
				sack_blocks[i].start,
				sack_blocks[i].end,
				(sack_blocks[i].end - sack_blocks[i].start));
		if (dump_out_sack) {
			print_out_space(out);
			fprintf(dump_out_sack, "SACK:%u:%u (%u)\n",
				sack_blocks[i].start,
				sack_blocks[i].end,
				(sack_blocks[i].end - sack_blocks[i].start));
		}
	}
	if (dump_out_sack) {
		print_out_space(out);
		fprintf(dump_out_sack, "DONE\n");
	}
}

static void
tcp_dooptions(struct tcpopt *to, const u_char *cp, int cnt, int flags)
{
	int opt, optlen;

	to->to_flags = 0;
	for (; cnt > 0; cnt -= optlen, cp += optlen) {
		opt = cp[0];
		if (opt == TCPOPT_EOL)
			break;
		if (opt == TCPOPT_NOP)
			optlen = 1;
		else {
			if (cnt < 2)
				break;
			optlen = cp[1];
			if (optlen < 2 || optlen > cnt)
				break;
		}
		switch (opt) {
		case TCPOPT_MAXSEG:
			if (optlen != TCPOLEN_MAXSEG)
				continue;
			if (!(flags & TO_SYN))
				continue;
			to->to_flags |= TOF_MSS;
			bcopy((const char *)cp + 2,
			    (char *)&to->to_mss, sizeof(to->to_mss));
			to->to_mss = ntohs(to->to_mss);
			break;
		case TCPOPT_WINDOW:
			if (optlen != TCPOLEN_WINDOW)
				continue;
			if (!(flags & TO_SYN))
				continue;
			to->to_flags |= TOF_SCALE;
			if (cp[2] < TCP_MAX_WINSHIFT)
				to->to_wscale = cp[2];
			else
				to->to_wscale = TCP_MAX_WINSHIFT;
			break;
		case TCPOPT_TIMESTAMP:
			if (optlen != TCPOLEN_TIMESTAMP)
				continue;
			to->to_flags |= TOF_TS;
			bcopy((const char *)cp + 2,
			    (char *)&to->to_tsval, sizeof(to->to_tsval));
			to->to_tsval = ntohl(to->to_tsval);
			bcopy((const char *)cp + 6,
			    (char *)&to->to_tsecr, sizeof(to->to_tsecr));
			to->to_tsecr = ntohl(to->to_tsecr);
			break;
		case TCPOPT_SACK_PERMITTED:
			if (optlen != TCPOLEN_SACK_PERMITTED)
				continue;
			if (!(flags & TO_SYN))
				continue;
			to->to_flags |= TOF_SACKPERM;
			break;
		case TCPOPT_SACK:
			if (optlen <= 2 || (optlen - 2) % TCPOLEN_SACK != 0)
				continue;
			if (flags & TO_SYN)
				continue;
			to->to_flags |= TOF_SACK;
			to->to_nsacks = (optlen - 2) / TCPOLEN_SACK;
			to->to_sacks = __DECONST(u_char *, (cp + 2));
			break;
		case TCPOPT_FAST_OPEN:
			if ((optlen != TCPOLEN_FAST_OPEN_EMPTY) &&
			    (optlen < TCP_FASTOPEN_MIN_COOKIE_LEN +
			    TCPOLEN_FAST_OPEN_EMPTY) &&
			    (optlen > TCP_FASTOPEN_MAX_COOKIE_LEN +
			    TCPOLEN_FAST_OPEN_EMPTY))
				continue;
			if (!(flags & TO_SYN))
				continue;
			to->to_flags |= TOF_FASTOPEN;
			to->to_tfo_len = optlen - 2;
			to->to_tfo_cookie = to->to_tfo_len ?
			    (__DECONST(u_char *, cp + 2)) : (u_char *)NULL;
			break;
		default:
			continue;
		}
	}
}

static void
process_options(struct tcpopt *to, const struct tcphdr *th,
    const uint8_t *optblk)
{
	int optlen;
	/* Process the tcp options */

	memset(to, 0, sizeof(struct tcpopt));
	if (th == NULL)
		return;	/* none :D */
	optlen = (th->th_off << 2) - sizeof (struct tcphdr);
	if (optlen <= 0)
		return;
	tcp_dooptions(to, (const u_char *)optblk, optlen, th->th_flags);
}

static const char *
translate_tcp_sock_option(uint32_t opt)
{
	if (opt == TCP_NODELAY) {
		return ("TCP_NODELAY");
	} else if (opt == TCP_MAXSEG) {
		return ("TCP_MAXSEG");
	} else if (opt == TCP_NOPUSH) {
		return ("TCP_NOPUSH");
	} else if (opt == TCP_NOOPT) {
		return ("TCP_NOOPT");
	} else if (opt == TCP_MD5SIG) {
		return ("TCP_MD5SIG");
	} else if (opt == TCP_INFO) {
		return ("TCP_INFO");
	} else if (opt == TCP_STATS) {
		return ("TCP_STATS");
	} else if (opt == TCP_LOG) {
		return ("TCP_LOG");
	} else if (opt == TCP_LOGBUF) {
		return ("TCP_LOGBUF");
	} else if (opt == TCP_LOGID) {
		return ("TCP_LOGID");
	} else if (opt == TCP_LOGDUMP) {
		return ("TCP_LOGDUMP");
	} else if (opt == TCP_LOGDUMPID) {
		return ("TCP_LOGDUMPID");
	} else if (opt == TCP_TXTLS_ENABLE) {
		return ("TCP_TXTLS_ENABLE");
	} else if (opt == TCP_TXTLS_MODE) {
		return ("TCP_TXTLS_MODE");
	} else if (opt == TCP_MAXBURST) {
		return ("TCP_MAXBURST");
	} else if (opt == TCP_IWND_NB) {
		return ("TCP_IWND_NB");
	} else if (opt == TCP_IWND_NSEG) {
		return ("TCP_IWND_NSEG");
	} else if (opt == TCP_LOGID_CNT) {
		return ("TCP_LOGID_CNT");
	} else if (opt == TCP_LOG_TAG) {
		return ("TCP_LOG_TAG");
	} else if (opt == TCP_USER_LOG) {
		return ("TCP_USER_LOG");
	} else if (opt == TCP_MAXUNACKTIME) {
		return ("TCP_MAXUNACKTIME");
	} else if (opt == TCP_MAXPEAKRATE) {
		return ("TCP_MAXPEAKRATE");
	} else if (opt == TCP_IDLE_REDUCE) {
		return ("TCP_IDLE_REDUCE");
	} else if (opt == TCP_REMOTE_UDP_ENCAPS_PORT) {
		return ("TCP_REMOTE_UDP_ENCAPS_PORT");
	} else if (opt == TCP_PROC_ACCOUNTING) {
		return ("TCP_PROC_ACCOUNTING");
	} else if (opt == TCP_CONGESTION) {
		return ("TCP_CONGESTION");
	} else if (opt == TCP_CCALGOOPT) {
		return ("TCP_CCALGOOPT");
	} else if (opt == TCP_DELACK) {
		return ("TCP_DELACK");
	} else if (opt == TCP_FIN_IS_RST) {
		return ("TCP_FIN_IS_RST");
	} else if (opt == TCP_LOG_LIMIT) {
		return ("TCP_LOG_LIMIT");
	} else if (opt == TCP_SHARED_CWND_ALLOWED) {
		return ("TCP_SHARED_CWND_ALLOWED");
	} else if (opt == TCP_KEEPINIT) {
		return ("TCP_KEEPINIT");
	} else if (opt == TCP_KEEPIDLE) {
		return ("TCP_KEEPIDLE");
	} else if (opt == TCP_KEEPINTVL) {
		return ("TCP_KEEPINTVL");
	} else if (opt == TCP_KEEPCNT) {
		return ("TCP_KEEPCNT");
	} else if (opt == TCP_FASTOPEN) {
		return ("TCP_FASTOPEN");
	} else if (opt == TCP_RACK_PROP) {
		return ("TCP_RACK_PROP");
	} else if (opt == TCP_RACK_TLP_REDUCE) {
		return ("TCP_RACK_TLP_REDUCE");
	} else if (opt == TCP_RACK_PACE_REDUCE) {
		return ("TCP_RACK_PACE_REDUCE");
	} else if (opt == TCP_RACK_PACE_MAX_SEG) {
		return ("TCP_RACK_PACE_MAX_SEG");
	} else if (opt == TCP_RACK_PACE_ALWAYS) {
		return ("TCP_RACK_PACE_ALWAYS");
	} else if (opt == TCP_RACK_PROP_RATE) {
		return ("TCP_RACK_PROP_RATE");
	} else if (opt == TCP_RACK_PRR_SENDALOT) {
		return ("TCP_RACK_PRR_SENDALOT");
	} else if (opt == TCP_RACK_MIN_TO) {
		return ("TCP_RACK_MIN_TO");
	} else if (opt == TCP_RACK_EARLY_RECOV) {
		return ("TCP_RACK_EARLY_RECOV");
	} else if (opt == TCP_RACK_EARLY_SEG) {
		return ("TCP_RACK_EARLY_SEG");
	} else if (opt == TCP_RACK_REORD_THRESH) {
		return ("TCP_RACK_REORD_THRESH");
	} else if (opt == TCP_RACK_REORD_FADE) {
		return ("TCP_RACK_REORD_FADE");
	} else if (opt == TCP_RACK_TLP_THRESH) {
		return ("TCP_RACK_TLP_THRESH");
	} else if (opt == TCP_RACK_PKT_DELAY) {
		return ("TCP_RACK_PKT_DELAY");
	} else if (opt == TCP_RACK_TLP_INC_VAR) {
		return ("TCP_RACK_TLP_INC_VAR");
	} else if (opt == TCP_BBR_IWINTSO) {
		return ("TCP_BBR_IWINTSO");
	} else if (opt == TCP_BBR_RECFORCE) {
		return ("TCP_BBR_RECFORCE");
	} else if (opt == TCP_BBR_STARTUP_PG) {
		return ("TCP_BBR_STARTUP_PG");
	} else if (opt == TCP_BBR_DRAIN_PG) {
		return ("TCP_BBR_DRAIN_PG");
	} else if (opt == TCP_BBR_RWND_IS_APP) {
		return ("TCP_BBR_RWND_IS_APP");
	} else if (opt == TCP_BBR_PROBE_RTT_INT) {
		return ("TCP_BBR_PROBE_RTT_INT");
	} else if (opt == TCP_BBR_ONE_RETRAN) {
		return ("TCP_BBR_ONE_RETRAN");
	} else if (opt == TCP_BBR_STARTUP_LOSS_EXIT) {
		return ("TCP_BBR_STARTUP_LOSS_EXIT");
	} else if (opt == TCP_BBR_USE_LOWGAIN) {
		return ("TCP_BBR_USE_LOWGAIN");
	} else if (opt == TCP_BBR_LOWGAIN_THRESH) {
		return ("TCP_BBR_LOWGAIN_THRESH");
	} else if (opt == TCP_BBR_TSLIMITS) {
		return ("TCP_BBR_TSLIMITS");
	} else if (opt == TCP_BBR_LOWGAIN_HALF) {
		return ("TCP_BBR_LOWGAIN_HALF");
	} else if (opt == TCP_BBR_PACE_OH) {
		return ("TCP_BBR_PACE_OH");
	} else if (opt == TCP_BBR_LOWGAIN_FD) {
		return ("TCP_BBR_LOWGAIN_FD");
	} else if (opt == TCP_BBR_HOLD_TARGET) {
		return ("TCP_BBR_HOLD_TARGET");
	} else if (opt == TCP_BBR_USEDEL_RATE) {
		return ("TCP_BBR_USEDEL_RATE");
	} else if (opt == TCP_BBR_MIN_RTO) {
		return ("TCP_BBR_MIN_RTO");
	} else if (opt == TCP_BBR_MAX_RTO) {
		return ("TCP_BBR_MAX_RTO");
	} else if (opt == TCP_BBR_REC_OVER_HPTS) {
		return ("TCP_BBR_REC_OVER_HPTS");
	} else if (opt == TCP_BBR_UNLIMITED) {
		return ("TCP_BBR_UNLIMITED");
	} else if (opt == TCP_BBR_ALGORITHM) {
		return ("TCP_BBR_ALGORITHM");
	} else if (opt == TCP_BBR_DRAIN_INC_EXTRA) {
		return ("TCP_BBR_DRAIN_INC_EXTRA");
	} else if (opt == TCP_BBR_STARTUP_EXIT_EPOCH) {
		return ("TCP_BBR_STARTUP_EXIT_EPOCH");
	} else if (opt == TCP_BBR_PACE_PER_SEC) {
		return ("TCP_BBR_PACE_PER_SEC");
	} else if (opt == TCP_BBR_PACE_DEL_TAR) {
		return ("TCP_BBR_PACE_DEL_TAR");
	} else if (opt == TCP_BBR_PACE_SEG_MAX) {
		return ("TCP_BBR_PACE_SEG_MAX");
	} else if (opt == TCP_BBR_PACE_SEG_MIN) {
		return ("TCP_BBR_PACE_SEG_MIN");
	} else if (opt == TCP_BBR_PACE_CROSS) {
		return ("TCP_BBR_PACE_CROSS");
	} else if (opt == TCP_RACK_IDLE_REDUCE_HIGH) {
		return ("TCP_RACK_IDLE_REDUCE_HIGH");
	} else if (opt == TCP_RACK_MIN_PACE) {
		return ("TCP_RACK_MIN_PACE");
	} else if (opt == TCP_RACK_MIN_PACE_SEG) {
		return ("TCP_RACK_MIN_PACE_SEG");
	} else if (opt == TCP_RACK_GP_INCREASE) {
		return ("TCP_RACK_GP_INCREASE");
	} else if (opt == TCP_RACK_TLP_USE) {
		return ("TCP_RACK_TLP_USE");
	} else if (opt == TCP_BBR_ACK_COMP_ALG) {
		return ("TCP_BBR_ACK_COMP_ALG");
	} else if (opt == TCP_BBR_TMR_PACE_OH) {
		return ("TCP_BBR_TMR_PACE_OH");
	} else if (opt == TCP_BBR_EXTRA_GAIN) {
		return ("TCP_BBR_EXTRA_GAIN");
	} else if (opt == TCP_RACK_DO_DETECTION) {
		return ("TCP_RACK_DO_DETECTION");
	} else if (opt == TCP_BBR_RACK_RTT_USE) {
		return ("TCP_BBR_RACK_RTT_USE");
	} else if (opt == TCP_BBR_RETRAN_WTSO) {
		return ("TCP_BBR_RETRAN_WTSO");
	} else if (opt == TCP_DATA_AFTER_CLOSE) {
		return ("TCP_DATA_AFTER_CLOSE");
	} else if (opt == TCP_BBR_PROBE_RTT_GAIN) {
		return ("TCP_BBR_PROBE_RTT_GAIN");
	} else if (opt == TCP_BBR_PROBE_RTT_LEN) {
		return ("TCP_BBR_PROBE_RTT_LEN");
	} else if (opt == TCP_BBR_SEND_IWND_IN_TSO) {
		return ("TCP_BBR_SEND_IWND_IN_TSO");
	} else if (opt == TCP_BBR_USE_RACK_RR) {
		return ("TCP_BBR_USE_RACK_RR");
	} else if (opt == TCP_BBR_HDWR_PACE) {
		return ("TCP_BBR_HDWR_PACE");
	} else if (opt == TCP_BBR_UTTER_MAX_TSO) {
		return ("TCP_BBR_UTTER_MAX_TSO");
	} else if (opt == TCP_BBR_EXTRA_STATE) {
		return ("TCP_BBR_EXTRA_STATE");
	} else if (opt == TCP_BBR_FLOOR_MIN_TSO) {
		return ("TCP_BBR_FLOOR_MIN_TSO");
	} else if (opt == TCP_BBR_MIN_TOPACEOUT) {
		return ("TCP_BBR_MIN_TOPACEOUT");
	} else if (opt == TCP_BBR_TSTMP_RAISES) {
		return ("TCP_BBR_TSTMP_RAISES");
	} else if (opt == TCP_BBR_POLICER_DETECT) {
		return ("TCP_BBR_POLICER_DETECT");
	} else if (opt == TCP_BBR_RACK_INIT_RATE) {
		return ("TCP_BBR_RACK_INIT_RATE");
	} else if (opt == TCP_RACK_RR_CONF) {
		return ("TCP_RACK_RR_CONF");
	} else if (opt == TCP_RACK_GP_INCREASE_CA) {
		return ("TCP_RACK_GP_INCREASE_CA");
	} else if (opt == TCP_RACK_GP_INCREASE_SS) {
		return ("TCP_RACK_GP_INCREASE_SS");
	} else if (opt == TCP_RACK_GP_INCREASE_REC) {
		return ("TCP_RACK_GP_INCREASE_REC");
	} else if (opt == TCP_RACK_FORCE_MSEG) {
		return ("TCP_RACK_FORCE_MSEG");
	} else if (opt == TCP_RACK_PACE_RATE_CA) {
		return ("TCP_RACK_PACE_RATE_CA");
	} else if (opt == TCP_RACK_PACE_RATE_SS) {
		return ("TCP_RACK_PACE_RATE_SS");
	} else if (opt == TCP_RACK_PACE_RATE_REC) {
		return ("TCP_RACK_PACE_RATE_REC");
	} else if (opt == TCP_NO_PRR) {
		return ("TCP_NO_PRR");
	} else if (opt == TCP_RACK_NONRXT_CFG_RATE) {
		return ("TCP_RACK_NONRXT_CFG_RATE");
	} else if (opt == TCP_SHARED_CWND_ENABLE) {
		return ("TCP_SHARED_CWND_ENABLE");
	} else if (opt == TCP_TIMELY_DYN_ADJ) {
		return ("TCP_TIMELY_DYN_ADJ");
	} else if (opt == TCP_RACK_NO_PUSH_AT_MAX) {
		return("TCP_RACK_NO_PUSH_AT_MAX");
	} else if (opt == TCP_RACK_PACE_TO_FILL) {
		return("TCP_RACK_PACE_TO_FILL");
	} else if (opt == TCP_RACK_MBUF_QUEUE) {
		return ("TCP_RACK_MBUF_QUEUE");
	} else if (opt == TCP_RACK_PROFILE) {
		return ("TCP_RACK_PROFILE");
	} else if (opt == TCP_HDWR_RATE_CAP) {
		return ("TCP_HDWR_RATE_CAP");
	} else if (opt == TCP_PACING_RATE_CAP) {
		return ("TCP_PACING_RATE_CAP");
	} else if (opt == TCP_HDWR_UP_ONLY) {
		return ("TCP_HDWR_UP_ONLY");
	} else if (opt == TCP_RACK_ABC_VAL) {
		return ("TCP_RACK_ABC_VAL");
	} else if (opt == TCP_REC_ABC_VAL) {
		return ("TCP_RECOVERY_ABC_VAL");
	} else if (opt == TCP_RACK_MEASURE_CNT) {
		return ("TCP_MEASURE_CNT");
	} else if (opt == TCP_DEFER_OPTIONS) {
		return ("TCP_DEFER_OPTIONS");
	} else if (opt == TCP_FAST_RSM_HACK) {
		return ("TCP_FAST_RSM_HACK");
	} else if (opt == TCP_RACK_PACING_BETA) {
		return ("TCP_RACK_PACING_BETA");
	} else if (opt == TCP_RACK_PACING_BETA_ECN) {
		return ("TCP_RACK_PACING_BETA_ECN");
	} else if (opt == TCP_RACK_TIMER_SLOP) {
		return ("TCP_RACK_TIMER_SLOP");
	} else if (opt == TCP_RACK_DSACK_OPT) {
		return ("TCP_RACK_DSACK_OPT");
	} else if (opt == TCP_RACK_ENABLE_HYSTART) {
		return ("TCP_RACK_ENABLE_HYSTART");
	} else if (opt == TCP_RACK_SET_RXT_OPTIONS) {
		return ("TCP_RACK_SET_RXT_OPTIONS");
	} else if (opt == TCP_RACK_HI_BETA) {
		return ("TCP_RACK_HI_BETA");
	} else if (opt == TCP_RACK_SPLIT_LIMIT) {
		return ("TCP_RACK_SPLIT_LIMIT");
	} else if (opt == TCP_RACK_PACING_DIVISOR) {
		return ("TCP_RACK_PACING_DIVISOR");
	} else if (opt == TCP_RACK_PACE_MIN_SEG) {
		return ("TCP_RACK_PACE_MIN_SEG");
	} else if (opt == TCP_RACK_DGP_IN_REC) {
		return ("TCP_RACK_DGP_IN_REC");
	} else if (opt == TCP_HYBRID_PACING) {
		return ("TCP_HYBRID_PACING");
	} else if (opt == TCP_PACING_DND) {
		return ("TCP_PACING_DND");
#ifdef NETFLIX_TCP_STACK
	} else if (opt == TCP_POLICER_DETECT) {
		return ("TCP_POLICER_DETECT");
	} else if (opt == TCP_SS_EEXIT) {
		return ("TCP_SS_EEXIT");
	} else if (opt == TCP_NO_TIMELY) {
		return ("TCP_NO_TIMELY");
	} else if (opt == TCP_HONOR_HPTS_MIN) {
		return ("TCP_HONOR_HPTS_MIN");
	} else if (opt == TCP_REC_IS_DYN) {
		return ("TCP_REC_IS_DYN");
	} else if (opt == TCP_FILLCW_RATE_CAP) {
		return ("TCP_FILLCW_RATE_CAP");
	} else if (opt == TCP_POLICER_MSS) {
		return ("TCP_POLICER_MSS");
#endif
	} else {
		static char buf[128];
		sprintf(buf, "Unknown? %d ", opt);
		return (buf);
	}
}

static void
display_pru(const struct tcp_log_buffer *l)
{
	fprintf(out, " pru_method:%s (%u) err:%u\n",
		prurequests[l->tlb_flex1],
		l->tlb_flex1, l->tlb_errno);
}

static void
display_tcp_option(const struct tcp_log_buffer *l)
{
	fprintf(out, "Option:%s(%u) Value:%u errno:%d fb:0%lx\n",
		translate_tcp_sock_option(l->tlb_flex1),
		l->tlb_flex1,
		l->tlb_flex2,
		l->tlb_errno,
		l->tlb_stackinfo.u_bbr.delRate);
}

static void
display_tp_trigger(const struct tcp_log_buffer *l)
{
	const struct tcp_log_bbr *bbr;

	bbr = &l->tlb_stackinfo.u_bbr;
	fprintf(out, " Line:%d TP Number:%u left:%u mapa:%u sd:%d\n",
		bbr->flex1,
		bbr->flex2,
		bbr->flex3,
		bbr->flex4, bbr->flex8);
}

static void
tcp_display_wakeup(const struct tcp_log_buffer *l, const struct tcp_log_bbr *bbr)
{
	int notify;
	/*
	 * SB_WAIT =  0x04
	 * SB_SEL  =  0x08
	 * SB_ASYNC = 0x10
	 * SB_UPCALL= 0x20
	 * SB_AIO   = 0x80
	 * SB_KNOTE = 0x100
	 */

	notify = bbr->flex1 & 0x1bc;
	if (bbr->flex8 == 1) {
		fprintf(out, "Read wakeup recv'd %d bytes -- sbflags 0x%x -- %s avail:%u out:%u sb_state:%u\n",
			bbr->flex2,
			bbr->flex1, ((notify) ? "will wake" : "will not wake"),
			l->tlb_rxbuf.tls_sb_acc,
			(l->tlb_snd_max - l->tlb_snd_una), bbr->flex3);
	} else {
		fprintf(out, "Write wakeup ack'd %u bytes -- sbflags 0x%x -- %s avail:%u out:%u sb_state:%u\n",
			bbr->flex2,  bbr->flex1, ((notify) ? "will wake" : "will not wake"),
			l->tlb_txbuf.tls_sb_acc, (l->tlb_snd_max - l->tlb_snd_una), bbr->flex3);
	}
}

static void
tcp_display_http_log(const struct tcp_log_buffer *l, const struct tcp_log_bbr * bbr)
{
	char buf[128];
	char flagtran[1024];
	const char *reas;
	if (bbr->flex8 == TCP_TRK_REQ_LOG_NEW)
		reas = "New entry";
	else if (bbr->flex8 == TCP_TRK_REQ_LOG_COMPLETE)
		reas = "Complete";
	else if (bbr->flex8 == TCP_TRK_REQ_LOG_FREED)
		reas = "Freed";
	else if (bbr->flex8 == TCP_TRK_REQ_LOG_ALLOCFAIL)
		reas = "Alloc Failure";
	else if (bbr->flex8 == TCP_TRK_REQ_LOG_MOREYET)
		reas = "More to come";
	else if (bbr->flex8 == TCP_TRK_REQ_LOG_FORCEFREE)
		reas = "Force Free";
	else if (bbr->flex8 == TCP_TRK_REQ_LOG_STALE)
		reas = "Stale";
	else {
		sprintf(buf, "Unknown:%d", bbr->flex8);
		reas = buf;
	}
	flagtran[0] = 0;
	if (bbr->flex3 == TCP_TRK_TRACK_FLG_EMPTY) {
		sprintf(flagtran, "Empty");
	} else {
		if (bbr->flex3 & TCP_TRK_TRACK_FLG_USED) {
			strcat(flagtran, "USED ");
		}
		if (bbr->flex3 & TCP_TRK_TRACK_FLG_OPEN) {
			strcat(flagtran, "OPEN ");
		}
		if (bbr->flex3 & TCP_TRK_TRACK_FLG_SEQV) {
			strcat(flagtran, "SEQV ");
		}
		if (bbr->flex3 & TCP_TRK_TRACK_FLG_COMP) {
			strcat(flagtran, "COMP ");
		}
		if (bbr->flex3 & TCP_TRK_TRACK_FLG_FSND) {
			strcat(flagtran,"FSND ");
		}

	}
	fprintf(out, " %s COcR:0x%x tm:%lu flg:%s(0x%x) [ %lu - ",
		reas,
		bbr->applimited,
		bbr->rttProp,
		flagtran,
		bbr->flex3,
		bbr->delRate);
	if (bbr->flex3 & TCP_TRK_TRACK_FLG_OPEN)  {
		fprintf(out, " ] slot:%d\n",
			bbr->flex7);
	} else {
		fprintf(out, " %lu (%lu) ] slot:%d\n",
			bbr->cur_del_rate,
			((bbr->cur_del_rate > bbr->delRate) ?
			 (bbr->cur_del_rate - bbr->delRate) : 0),
			bbr->flex7);
	}
	if (extra_print) {
		uint64_t nbytes, ltime;
		uint64_t cspr;
		uint32_t seq_off;

		nbytes = bbr->flex6;
		nbytes <<= 32;
		nbytes |= bbr->epoch;
		ltime = bbr->flex4;
		ltime <<= 32;
		ltime |= bbr->flex5;
		print_out_space(out);
		if (bbr->flex3 & TCP_TRK_TRACK_FLG_OPEN)  {
			if (SEQ_GT(l->tlb_snd_una, bbr->flex1))
				seq_off = l->tlb_snd_una;
			else
				seq_off = bbr->flex1;
		} else
			seq_off = bbr->flex2;
		fprintf(out, "offset:%lu [tcp sseq:%u eseq:%u (%u) sndmax:%u snduna:%u] sb_acc:%u sb_ccc:%u\n",
			bbr->bw_inuse,
			bbr->flex1, bbr->flex2, (seq_off - bbr->flex1),
			l->tlb_snd_max, l->tlb_snd_una,
			l->tlb_txbuf.tls_sb_acc,
			l->tlb_txbuf.tls_sb_ccc);

		cspr = bbr->lt_epoch;
		cspr <<= 32;
		cspr |= bbr->pkts_out;
		print_out_space(out);
		fprintf(out, "cspr:%lu nbytes:%lu localtime:%lu \n",
			cspr, nbytes, ltime);
		if ((bbr->flex8 == TCP_TRK_REQ_LOG_FREED) &&
		    ((bbr->flex3 & TCP_TRK_TRACK_FLG_OPEN) == 0)) {
			/* calculate the bw req/to/comp */
			uint32_t conv_time;

			print_out_space(out);
			conv_time = (uint32_t)ltime;
			if (TSTMP_GT(bbr->timeStamp, conv_time)) {
				uint64_t btf, calc_bw;
				uint32_t tim;

				tim = bbr->timeStamp - conv_time;
				if (bbr->cur_del_rate > bbr->delRate)
					btf = (bbr->cur_del_rate - bbr->delRate);
				else
					btf = 0;
				calc_bw = btf * 1000000;
				calc_bw /= tim;

				fprintf(out,
					"bytes:%lu tim:%u tfx at:%s (%lu)\n",
					btf, tim,
					display_bw(calc_bw, 0), calc_bw);
			} else {
				fprintf(out, "Timestamp:%u <= time:%u bytes txf:%lu\n",
					conv_time, bbr->timeStamp,
					(bbr->cur_del_rate - bbr->delRate));
			}
		}
	}
}

static int include_user_send = 0;

static const char *
get_jr_reason(uint32_t reas)
{
	static char ret_string[100];
	if (reas == CTF_JR_SENT_DATA)
		sprintf(ret_string, "Done Sending %d", reas);
	else if (reas == CTF_JR_CWND_LIMITED)
		sprintf(ret_string, "CWND Limited %d", reas);
	else if (reas == CTF_JR_RWND_LIMITED)
		sprintf(ret_string, "RWND Limited %d", reas);
	else if (reas == CTF_JR_APP_LIMITED)
		sprintf(ret_string, "APP Limited %d", reas);
	else if (reas == CTF_JR_PERSISTS)
		sprintf(ret_string, "Persists %d", reas);
	else if (reas == CTF_JR_ASSESSING)
		sprintf(ret_string, "Assessing %d", reas);
	else if (reas == CTF_JR_PRR)
		sprintf(ret_string, "Prr %d", reas);
	else
		sprintf(ret_string, "unknown:%d?", reas);
	return (ret_string);
}

#define SHRINKS_LAST 12
static const char *shrinks_reasons[] = {
	"RTTS Initial setting",
	"RTTS Measured new lower RTT",
	"RTTS Exiting ProbeRTT",
	"RTTS Was Idle",
	"RTTS Persits",
	"RTTS Reaches Target",
	"RTTS Enter Probe RTT",
	"RTTS Shrinks pg",
	"RTTS Shrinks pg final",
	"RTTS New Target",
	"RTTS Leaves drain",
	"RTTS resets values",
	"RTTS Unknown"
};

static int show_record = 0;
static int ann_end = 0;

#define TCP_R_LOG_ADD		1
#define TCP_R_LOG_LIMIT_REACHED 2
#define TCP_R_LOG_APPEND	3
#define TCP_R_LOG_PREPEND	4
#define TCP_R_LOG_REPLACE	5
#define TCP_R_LOG_MERGE_INTO	6
#define TCP_R_LOG_NEW_ENTRY	7
#define TCP_R_LOG_READ		8
#define TCP_R_LOG_ZERO		9
#define TCP_R_LOG_DUMP		10
#define TCP_R_LOG_TRIM		11

static int is_bbr = 0;
static int state_is_set = 0;
static int minor_is_set = 0;
static int major_stateval = 0;
static int minor_state = 0;
static int state_transition_time = 0;
static int minor_state_transition_time = 0;
static uint64_t time_in_major_states[5];
static uint64_t time_in_sub_states[9];
static int last_state_policed = 0;

static uint32_t last_time_stamp = 0;

#ifdef DO_SIMPLE_ACCOUNTING

static void
do_state_accounting(const struct tcp_log_bbr *bbr)
{
	if (state_is_set == 0) {
		state_transition_time = bbr->timeStamp;
		major_stateval = bbr->bbr_state;
		state_is_set = 1;
		if (major_stateval == BBR_STATE_PROBE_BW) {
			minor_state_transition_time = bbr->timeStamp;
			minor_state = bbr->bbr_substate;
			minor_is_set = 1;
		}
	} else {
		if (major_stateval != bbr->bbr_state) {
			/* We have a new major state */
			if (TSTMP_GT(bbr->timeStamp, state_transition_time))
				time_in_major_states[(major_stateval-1)] += (bbr->timeStamp - state_transition_time);
			if (major_stateval == BBR_STATE_PROBE_BW) {
				/* Do minor accounting too */
				if (bbr->use_lt_bw == 0) {
					if (TSTMP_GT(bbr->timeStamp, minor_state_transition_time))
						time_in_sub_states[minor_state] += bbr->timeStamp - minor_state_transition_time;
				} else {
					/* All policed */
					time_in_sub_states[8] += (bbr->timeStamp -
								  minor_state_transition_time);
				}
			}
			major_stateval = bbr->bbr_state;
			state_transition_time = bbr->timeStamp;
			if (major_stateval == BBR_STATE_PROBE_BW) {
				minor_state_transition_time = bbr->timeStamp;
				minor_state = bbr->bbr_substate;
				minor_is_set = 1;
			}
		} else if (major_stateval == BBR_STATE_PROBE_BW) {
			/* We have a new sub-state */
			if (minor_is_set == 0) {
				/* First time */
				minor_state_transition_time = bbr->timeStamp;
				minor_is_set = 1;
			} else {
				if (bbr->use_lt_bw == 0) {
					if (TSTMP_GT(bbr->timeStamp, minor_state_transition_time))
						time_in_sub_states[minor_state] += bbr->timeStamp - minor_state_transition_time;
				} else {
					time_in_sub_states[8] += (bbr->timeStamp -
								  minor_state_transition_time);
				}
				minor_state_transition_time = bbr->timeStamp;
			}
			minor_state = bbr->bbr_substate;
		}
	}
	if (bbr->use_lt_bw)
		last_state_policed = 1;
	else
		last_state_policed = 0;
}

#else

static void
do_state_accounting(const struct tcp_log_bbr *bbr)
{
	if (state_is_set == 0) {
		state_transition_time = bbr->timeStamp;
		major_stateval = bbr->bbr_state;
		state_is_set = 1;
		if (major_stateval == BBR_STATE_PROBE_BW) {
			minor_state_transition_time = bbr->timeStamp;
			minor_state = bbr->bbr_substate;
			minor_is_set = 1;
		}
	} else {
		if (major_stateval != bbr->bbr_state) {
			/* We have a new major state */
			if (TSTMP_GT(bbr->timeStamp, state_transition_time))
				time_in_major_states[(major_stateval-1)] += (bbr->timeStamp - state_transition_time);
			if (major_stateval == BBR_STATE_PROBE_BW) {
				/* Do minor accounting too */
				if ((bbr->use_lt_bw == 0) && (last_state_policed == 0)) {
					if (TSTMP_GT(bbr->timeStamp, minor_state_transition_time))
						time_in_sub_states[minor_state] += bbr->timeStamp - minor_state_transition_time;
				} else {
					/* policing action */
					if (last_state_policed && bbr->use_lt_bw) {
						/* All policed */
						time_in_sub_states[8] += (bbr->timeStamp -
									  minor_state_transition_time);
					} else if (bbr->use_lt_bw) {
						/* Switched to policing this time */
						if (TSTMP_GEQ(time_started_using_ltbw, minor_state_transition_time)) {
							time_in_sub_states[minor_state] += (time_started_using_ltbw -
											    minor_state_transition_time);
						} else {
							printf("1:Switch on minor:%d start_ltbw:%u minor_state:%u?\n",
							       minor_state,
							       time_started_using_ltbw,
							       minor_state_transition_time);
						}
						if (TSTMP_GEQ(bbr->timeStamp, time_started_using_ltbw)) {
							time_in_sub_states[8] += (bbr->timeStamp -
										  time_started_using_ltbw);
						} else {
							printf("2:Switched on minor:%d now:%u start_ltbw:%u?\n",
							       minor_state,
							       bbr->timeStamp,
							       time_started_using_ltbw);
						}
					} else {
						/* Switched off of policing */
						if (TSTMP_GEQ(time_ended_using_lt_bw, minor_state_transition_time)) {
							time_in_sub_states[8] += (time_ended_using_lt_bw -
										  minor_state_transition_time);
						} else {
							printf("1:Switch off minor:%d end_ltbw:%u minor_state:%u?\n",
							       minor_state,
							       time_ended_using_lt_bw,
							       minor_state_transition_time);

						}
						if (TSTMP_GEQ(bbr->timeStamp, time_ended_using_lt_bw)) {
							time_in_sub_states[minor_state] +=  (bbr->timeStamp -
											     time_ended_using_lt_bw);
						} else {
							printf("2:Switched off minor:%d now:%u end_ltbw:%u?\n",
							       minor_state,
							       bbr->timeStamp,
							       time_ended_using_lt_bw);
						}
					}
				}
			}
			major_stateval = bbr->bbr_state;
			state_transition_time = bbr->timeStamp;
			if (major_stateval == BBR_STATE_PROBE_BW) {
				minor_state_transition_time = bbr->timeStamp;
				minor_state = bbr->bbr_substate;
				minor_is_set = 1;
			}
		} else if (major_stateval == BBR_STATE_PROBE_BW) {
			/* We have a new sub-state */
			if (minor_is_set == 0) {
				/* First time */
				minor_state_transition_time = bbr->timeStamp;
				minor_is_set = 1;
			} else {
				if ((bbr->use_lt_bw == 0) && (last_state_policed == 0)) {
					if (TSTMP_GT(bbr->timeStamp, minor_state_transition_time))
						time_in_sub_states[minor_state] += bbr->timeStamp - minor_state_transition_time;
				} else {
					/* policing action */
					if (last_state_policed && bbr->use_lt_bw) {
						/* All policed */
						time_in_sub_states[8] += (bbr->timeStamp -
									  minor_state_transition_time);
					} else if ((bbr->use_lt_bw) && (last_state_policed == 0)) {
						/* Switched to policing this time */
						if (TSTMP_GEQ(time_started_using_ltbw, minor_state_transition_time)) {
							time_in_sub_states[minor_state] += (time_started_using_ltbw -
											    minor_state_transition_time);
						} else {
							printf("3:Switch on minor:%d start_ltbw:%u minor_state:%u?\n",
							       minor_state,
							       time_started_using_ltbw,
							       minor_state_transition_time);
						}
						if (TSTMP_GEQ(bbr->timeStamp, time_started_using_ltbw)) {
							time_in_sub_states[8] += (bbr->timeStamp -
										  time_started_using_ltbw);
						} else {
							printf("4:Switched on minor:%d now:%u start_ltbw:%u?\n",
							       minor_state,
							       bbr->timeStamp,
							       time_started_using_ltbw);
						}
					} else if ((bbr->use_lt_bw == 0) && (last_state_policed == 1)) {
						/* Switched off of policing */
						if (TSTMP_GEQ(time_ended_using_lt_bw, minor_state_transition_time)) {
							time_in_sub_states[8] += (time_ended_using_lt_bw -
										  minor_state_transition_time);
						} else {
							printf("3:Switch off minor:%d end_ltbw:%u minor_state:%u?\n",
							       minor_state,
							       time_ended_using_lt_bw,
							       minor_state_transition_time);

						}
						if (TSTMP_GEQ(bbr->timeStamp, time_ended_using_lt_bw)) {
							time_in_sub_states[minor_state] +=  (bbr->timeStamp -
											     time_ended_using_lt_bw);
						} else {
							printf("4:Switched off minor:%d now:%u end_ltbw:%u?\n",
							       minor_state,
							       bbr->timeStamp,
							       time_ended_using_lt_bw);
						}
					} else {
						fprintf(stdout, "Huh???\n");
					}
				}
				minor_state_transition_time = bbr->timeStamp;
			}
			minor_state = bbr->bbr_substate;
		}
	}
	if (bbr->use_lt_bw)
		last_state_policed = 1;
	else
		last_state_policed = 0;
}
#endif

static void
print_tcp_log_reass(const struct tcp_log_buffer *l,
		    const struct tcp_log_bbr *bbr)
{
	const char *frm;
	char buf[25];

	if (bbr->flex8 == TCP_R_LOG_ADD) {
		frm = "log add";
	} else if (bbr->flex8 == TCP_R_LOG_LIMIT_REACHED) {
		frm = "log limited";
	} else if (bbr->flex8 == TCP_R_LOG_APPEND) {
		frm = "log append";
	} else if (bbr->flex8 == TCP_R_LOG_PREPEND) {
		frm = "log prepend";
	} else if (bbr->flex8 == TCP_R_LOG_REPLACE) {
		frm = "log replace";
	} else if (bbr->flex8 == TCP_R_LOG_MERGE_INTO) {
		frm = "log merge info";
	} else if (bbr->flex8 == TCP_R_LOG_NEW_ENTRY) {
		frm = "log new entry";
	} else if (bbr->flex8 == TCP_R_LOG_READ) {
		frm = "log read";
	} else if (bbr->flex8 == TCP_R_LOG_ZERO) {
		frm = "log zero";
	} else if (bbr->flex8 == TCP_R_LOG_DUMP) {
		frm = "log dump";
	} else if (bbr->flex8 == TCP_R_LOG_TRIM) {
		frm = "log trim";
	} else {
		sprintf(buf, "U:%d", bbr->flex8);
		frm = buf;
	}
	fprintf(out, "%s ins:%d ", frm, bbr->flex7);
	if (bbr->cur_del_rate)
		fprintf(out, "q:0x%lx ",
			bbr->cur_del_rate);

	if (bbr->delRate)
		fprintf(out, "p:0x%lx ",
			bbr->delRate);
	if (bbr->flex8 == TCP_R_LOG_TRIM)
		fprintf(out, "trim passed %d ", l->tlb_len);
	else if (bbr->flex8 != TCP_R_LOG_DUMP)
		fprintf(out, "seq:%u(%d) tpsegl:%u ",
			bbr->flex1, l->tlb_len,
			bbr->flex6);
	if (bbr->cur_del_rate != 0) {
		fprintf(out, "qseq:%u(%d) flag:0x%x mblim:%u ",
			bbr->flex2,
			bbr->flex3,
			bbr->flex4, bbr->pacing_gain);
	}
	if (bbr->delRate != 0) {
		fprintf(out, "pseq:%u(%d) flags:0x%x mblin:%u ",
			bbr->flex5,
			bbr->pkts_out,
			bbr->epoch, bbr->cwnd_gain);
	}
	fprintf(out, "ur:%u\n", l->tlb_rxbuf.tls_sb_acc);
}

static uint64_t endcode = 0;
static uint32_t first_seq = 0;
static uint32_t last_snd_una = 0;

static void
get_end_code_string(uint64_t val, char *arry)
{
	int i;
	union foo {
		uint8_t t_bytes[TCP_END_BYTE_INFO];
		uint64_t t_value;
	} fee;

	if (val == 0) {
		strcpy(arry, "<NONE>");
		return;
	}
	fee.t_value = val;
	for(i = 0; i < TCP_END_BYTE_INFO; i++) {
		if (fee.t_bytes[i] == TCP_EI_EMPTY_SLOT)
			break;
		if (i > 0)
			strcat(arry, ",");
		if (fee.t_bytes[i] == TCP_EI_STATUS_PROGRESS)
			strcat(arry, "<PROGT>");
		else if (fee.t_bytes[i] == TCP_EI_STATUS_RETRAN)
			strcat(arry, "<RXTT>");
		else if (fee.t_bytes[i] == TCP_EI_STATUS_CLIENT_FIN)
			strcat(arry, "<FINC>");
		else if (fee.t_bytes[i] == TCP_EI_STATUS_CLIENT_RST)
			strcat(arry, "<RSTC>");
		else if (fee.t_bytes[i] == TCP_EI_STATUS_SERVER_FIN)
			strcat(arry, "<FINS>");
		else if (fee.t_bytes[i] == TCP_EI_STATUS_SERVER_RST)
			strcat(arry, "<RSTS>");
		else if (fee.t_bytes[i] == TCP_EI_STATUS_PERSIST_MAX)
			strcat(arry, "<PERT>");
		else if (fee.t_bytes[i] == TCP_EI_STATUS_DATA_A_CLOSE)
			strcat(arry, "<DACL>");
		else if (fee.t_bytes[i] == TCP_EI_STATUS_RST_IN_FRONT)
			strcat(arry, "<RSFS>");
		else if (fee.t_bytes[i] == TCP_EI_STATUS_2MSL)
			strcat(arry, "<2MSL>");
		else if (fee.t_bytes[i] == TCP_EI_STATUS_KEEP_MAX)
			strcat(arry, "<KEEP>");
		else {
			strcat(arry, "<?>");
		}

	}
}

static void
display_change_query(const struct tcp_log_buffer *l,
		       const struct tcp_log_bbr *bbr)
{
	if ((bbr->flex8 == 1) || (bbr->flex8 == 3)) {
		if (bbr->flex8 == 1)
			fprintf(out, " Change mod:existing:rsm query ");
		else
			fprintf(out, " Change mod:new:rsm query response ");
		fprintf(out, "snd_una:%u snd_max:%u r_start:%u r_end:%u ack:0x%x\n",
		       l->tlb_snd_una, l->tlb_snd_max,
		       bbr->flex1, bbr->flex2, bbr->flex3);
	} else if ((bbr->flex8 == 2) || (bbr->flex8 == 4)) {
		const char *mask;

		mask = get_timer_mask(bbr->flex1);
		if (bbr->flex8 == 2)
			fprintf(out, " Change mod:existing:timer query ");
		else
			fprintf(out, " Change mod:new:timer query ");
		fprintf(out, "Timer mask:%s (0x%x) po_exp:%u tmr_exp:%u\n",
		       mask, bbr->flex1, bbr->flex2, bbr->flex3);
	} else if (bbr->flex8 == 5) {
		fprintf(out, "Set to handle these inp2 flags 0x%x\n",
			bbr->flex1);
	} else if (bbr->flex8 == 6) {
		fprintf(out, "Load rack values rack_min_rtt:%u rack_rtt:%u reorder_ts:%u\n",
			bbr->flex1,
			bbr->flex2,
			bbr->flex3);
	} else if (bbr->flex8 == 7) {
		fprintf(out, "Change query - no_query set set to %u\n",
			bbr->flex1);
	} else {
		fprintf(out, " Unknown change query %u\n", bbr->flex8);
	}
}

static void
display_connection_end(const struct tcp_log_buffer *l,
		       const struct tcp_log_bbr *bbr)
{
	char arry[1024];

	memset(arry, 0, sizeof(arry));
	first_seq = l->tlb_iss;
	last_snd_una = l->tlb_snd_una;
	get_end_code_string(bbr->cur_del_rate, arry);
	endcode = bbr->cur_del_rate;
	fprintf(out, "***Connection Ends - transfers %u bytes, endcode 0x%lx (%s)\n",
		(last_snd_una - first_seq),
		bbr->cur_del_rate, arry);
}

static uint64_t sock_opt_cnt = 0;
static uint32_t lro_flush_time = 0;
static int lro_flush_is_ms = 0;

static const char *
hybrid_mode(uint8_t m)
{
	static char buf[100];

	if (m == HYBRID_LOG_NO_ROOM) {
		return ("HYBRID_LOG_NO_ROOM");
	} else if (m == HYBRID_LOG_TURNED_OFF) {
		return ("HYBRID_LOG_TURNED_OFF");
	} else if (m == HYBRID_LOG_NO_PACING) {
		return ("HYBRID_LOG_NO_PACING");
	} else if (m == HYBRID_LOG_RULES_SET) {
		return ("HYBRID_LOG_RULES_SET");
	} else if (m == HYBRID_LOG_NO_RANGE) {
		return ("HYBRID_LOG_NO_RANGE");
	} else if (m == HYBRID_LOG_RULES_APP) {
		return ("HYBRID_LOG_RULES_APP");
	} else if (m == HYBRID_LOG_REQ_COMP) {
		return ("HYBRID_LOG_REQ_COMP");
	} else if (m == HYBRID_LOG_BW_MEASURE) {
		return ("HYBRID_LOG_BW_MEASURE");
	} else if (m == HYBRID_LOG_RATE_CAP) {
		return ("HYBRID_LOG_RATE_CAP");
	} else if (m == HYBRID_LOG_CAP_CALC) {
		return ("HYBRID_LOG_RATE_CALC");
	} else if (m == HYBRID_LOG_ISSAME) {
		return ("HYBRID_LOG_ISSAME");
	} else if (m == HYBRID_LOG_ALLSENT) {
		return ("HYBRID_LOG_ALLSENT");
	} else if (m == HYBRID_LOG_OUTOFTIME) {
		return ("HYBRID_LOG_OUTOFTIME");
	} else if (m == HYBRID_LOG_CAPERROR) {
		return ("HYBRID_LOG_CAPERROR");
	} else if (m == HYBRID_LOG_EXTEND) {
		return ("HYBRID_LOG_EXTEND");
	} else if (m == HYBRID_LOG_SENT_LOST) {
		return ("HYBRID_LOG_SENT_LOST");
	}
	sprintf(buf, "Unknown:%u", m);
	return (buf);
}

static const char *
hybrid_flags(uint32_t flags)
{
	static char buf[512];

	if (flags & TCP_HYBRID_PACING_ENABLE) {
		strcpy(buf, "Enabled");
	} else {
		strcpy(buf, "Disabled");
	}
	if (flags & TCP_HYBRID_PACING_CU) {
		strcat(buf, "|CU");
	}
	if (flags & TCP_HYBRID_PACING_DTL) {
		strcat(buf, "|DL");
	}
	if (flags & TCP_HYBRID_PACING_CSPR) {
		strcat(buf, "|CSPR");
	}
	if (flags & TCP_HYBRID_PACING_H_MS) {
		strcat(buf, "|HINT_MSS");
	}
#ifdef NETFLIX_TCP_STACK
	if (flags & TCP_HAS_PLAYOUT_MS) {
		strcat(buf, "|PLAY_MS");
	}
	if (flags & TCP_HYBRID_PACING_SENDTIME) {
		strcat(buf, "|USE_ST");
	}
#endif
	return (buf);
}

static uint64_t prev_set_seen = 0;
static uint8_t prev_set_init = 0;

static const char *
get_hybrid_pacing_flags(uint8_t flg)
{
	static char flags_ret[512];
	size_t len;

	flags_ret[0] = 0;
	if (flg & 0x08) {
		strcat(flags_ret, "PACE_ALWAYS|");
	}
	if (flg & 0x04)
		strcat(flags_ret, "DGP_ON|");
	if (flg & 0x02)
		strcat(flags_ret, "HYBRID_ON|");
	if (flg & 0x01)
		strcat(flags_ret, "FIXED_RATE|");

	len = strlen(flags_ret);
	if (len == 0) {
		/* No hybrid  flags*/
		sprintf(flags_ret, "NOT PACED|HYBRID OFF"); 
	} else {
		/* Take out the trailing | */
		flags_ret[(len - 1)] = 0;
	}
	return (flags_ret);
}

static void
display_hybrid_pacing(const struct tcp_log_buffer *l, const struct tcp_log_bbr *bbr)
{
	if ((bbr->flex8 != HYBRID_LOG_BW_MEASURE) &&
	    (bbr->flex8 != HYBRID_LOG_RATE_CAP) &&
	    (bbr->flex8 != HYBRID_LOG_SENT_LOST) &&
	    (bbr->flex8 != HYBRID_LOG_CAP_CALC)) {
		uint64_t cur_time, since_prev_set = 0;

		cur_time = tcp_tv_to_lusectick(&l->tlb_tv);
		if (bbr->flex8 == HYBRID_LOG_RULES_SET) {
			if (prev_set_init) {
				since_prev_set = cur_time - prev_set_seen;
			}
			prev_set_seen = cur_time;
			prev_set_init = 1;
		}
		fprintf(out, "Reason:%s line:%d CHD:0x%x snd_una:%u ccap:%s(%lu) starts:%u stop:%u err:%u cs_mss:%u idx:%u Flags:%s\n",
			hybrid_mode(bbr->flex8),
			bbr->cwnd_gain,
			bbr->flex7, l->tlb_snd_una, display_bw(bbr->delRate, 0),
			bbr->delRate, bbr->pkt_epoch, bbr->pacing_gain, bbr->lost, bbr->bbr_substate,  bbr->use_lt_bw,
			get_hybrid_pacing_flags(bbr->bbr_state));
		if (extra_print) {
			print_out_space(out);
			if (bbr->inhpts == 1) {
				uint64_t end, deadline, localtime;

				end = bbr->delivered;
				end <<= 32;
				end |= bbr->applimited;
				deadline = bbr->lt_epoch;
				deadline <<= 32;
				deadline |= bbr->epoch;
				localtime = bbr->flex4;
				localtime <<= 32;
				localtime |= bbr->flex5;

				fprintf(out, "mode:%s SENDFILE  Start:%lu End:%lu Pre_seqs:%u Pre_seqe:%u ",
					hybrid_mode(bbr->flex8),
					bbr->bw_inuse, end,
					bbr->flex2, bbr->flex3);
				if (bbr->flex8 == HYBRID_LOG_RULES_SET) {
					fprintf(out,"[since_prev_set %lu]\n", since_prev_set);
				} else {
					fprintf(out, "\n");
				}
				print_out_space(out);
				fprintf(out, "Client Timestamp:%lu Localtime:%lu deadline:%lu\n",
					bbr->rttProp, localtime, deadline);
				print_out_space(out);
				fprintf(out, "Cspr:%s(%lu) flags:0x%x hybrid_flags:%s (0x%x)\n",
					display_bw(bbr->cur_del_rate, 0), bbr->cur_del_rate,
					bbr->flex6,
					hybrid_flags(bbr->pkts_out),
					bbr->pkts_out);
				if (bbr->flex8 == HYBRID_LOG_REQ_COMP) {
					uint64_t req_to_comp, bytes_in_req, comp_us, desired_comp_time;

					print_out_space(out);
					req_to_comp = cur_time - localtime;
					fprintf(out, "SENDFILE Start:%lu Time req2comp:%lu",
						bbr->bw_inuse,
						req_to_comp);
					if (bbr->cur_del_rate > 0) {
						bytes_in_req = end - bbr->bw_inuse;
						/* Derive the desired time of completion */
						comp_us = (bytes_in_req * (uint64_t)1000000) / bbr->cur_del_rate;
						/*
						 * Now lets take the time we got the request plus this time
						 * to derive the anticipated completion time by the client.
						 */
						desired_comp_time = localtime + comp_us;
						fprintf(out, " Client desired comp time %lu",
							comp_us);
						if (desired_comp_time < cur_time) {
							fprintf(out, " Outcome Late by %lu\n",
								(cur_time - desired_comp_time));
						} else if (desired_comp_time == cur_time) {
							fprintf(out, " Outcome exactly on time\n");
						} else {
							fprintf(out, " Outcome early by %lu\n",
								(desired_comp_time - cur_time));
						}
					} else {
						fprintf(out, " No CSPR to estimate client end time\n");
					}
				}
			} else {
				fprintf(out, "Seq:%u No http entry err:%d\n",
				bbr->flex1, bbr->flex2);
			}
		}
	} else if (bbr->flex8 == HYBRID_LOG_SENT_LOST) {
		uint64_t sent, rxt, fs, now, fs_rxt, now_rxt;
		uint64_t last_send_time;

		now = bbr->cur_del_rate;
		fs = bbr->delRate;
		sent = now - fs;
		now_rxt = bbr->rttProp;
		fs_rxt = bbr->bw_inuse;
		rxt = now_rxt - fs_rxt;
		last_send_time = bbr->flex5;
		last_send_time <<= 32;
		last_send_time |= bbr->pkt_epoch;
		fprintf(out, "Reason:%s line:%d hybrid_flags:%s Sent:%lu Rxt:%lu idx:%d Flags:%s\n",
			hybrid_mode(bbr->flex8),
			bbr->cwnd_gain, hybrid_flags(bbr->pkts_out),
			sent, rxt, bbr->bbr_substate, get_hybrid_pacing_flags(bbr->bbr_state));
		if (extra_print) {
			print_out_space(out);
			fprintf(out, "sent_cur:%lu sent_fs:%lu rxt_cur:%lu rxt_fs:%lu last_send_time:%lu f5:%u pe:%u play_ms:%u\n",
				bbr->cur_del_rate,
				bbr->delRate,
				bbr->rttProp,
				bbr->bw_inuse, last_send_time,
				bbr->flex5, bbr->pkt_epoch, bbr->lost);
		}
	} else if (bbr->flex8 == HYBRID_LOG_BW_MEASURE) {
		/* the measure is special */
		uint64_t ltbw, start, end, data, i_cbw;
		uint64_t localtime, sendtime, chk_tim;

		/* start = < lost | pkt_epoch > */
		start = bbr->lost;
		start <<= 32;
		start |= bbr->pkt_epoch;
		/* end = < pkts_out | flex6 > */
		end = bbr->pkts_out;
		end <<= 32;
		end |= bbr->flex6;
		ltbw = bbr->flex3;
		ltbw <<= 32;
		ltbw |= bbr->flex2;
		data = end - start;
		/* localtime = <delivered | applimited>*/
		localtime = bbr->delivered;
		localtime <<= 32;
		localtime |= bbr->applimited;
		/* first_send = <lt_epoch | epoch> */
		sendtime = bbr->lt_epoch;
		sendtime <<= 32;
		sendtime |= bbr->epoch;
		/* Come up with the actual cbw from start */
		chk_tim = bbr->rttProp;
		if (sendtime > localtime) {
			chk_tim += (sendtime - localtime);
		}
		i_cbw = data * 1000000;
		i_cbw /= chk_tim;
		fprintf(out, "Reason:%s cbw:%s (%lu) data:%lu tim:%lu idx:%u",
			hybrid_mode(bbr->flex8),
			display_bw(bbr->bw_inuse, 0), bbr->bw_inuse,
			data,
			bbr->rttProp,
			bbr->bbr_substate);
			
		fprintf(out, " i_cbw:%s (%lu)\n",
			display_bw(i_cbw, 0), i_cbw);
		print_out_space(out);
		fprintf(out, "GP est:%s (%lu) seq:%u ",
			display_bw(bbr->delRate, 0), bbr->delRate, bbr->flex1);
		fprintf(out, "LTBW:%s (%lu) start:%lu end:%lu ",
			display_bw(ltbw,0), ltbw, start, end);
		if (bbr->inflight != 0) {
			/* We have a last RTT to make another more accurate b/w meas */
			uint64_t c_bw, rttc;
			char cc;

			c_bw = end - start;
			c_bw *= 1000000;
			if (bbr->inflight < bbr->rttProp) {
				rttc = bbr->rttProp;
				rttc -= bbr->inflight;
				cc = ' ';
			} else {
				rttc = bbr->rttProp;
				cc = '*';
			}
			if (rttc == 0) {
				rttc = 1;
				cc = '^';
			}
			c_bw /= rttc;
			fprintf(out, " lastrtt:%u bw_mrtt:%s (%lu)%c\n",
				bbr->inflight, display_bw(c_bw, 0), c_bw, cc);
		} else {
			fprintf(out, " - no rtt avail\n");
		}
		if (extra_print) {
			print_out_space(out);
			if (sendtime == 0) {
				fprintf(out, "No first send time recorded, num_of_bytes_sent:%u  num_of_rxt_bytes:%u Flags:%s \n",
					bbr->flex4, bbr->flex5,  get_hybrid_pacing_flags(bbr->bbr_state));
			} else {
				fprintf(out, "Time_delay_to_send:%ld num_of_bytes_sent:%u  num_of_rxt_bytes:%u Flags:%s fst:%lu\n",
					(sendtime - localtime), bbr->flex4, bbr->flex5,  get_hybrid_pacing_flags(bbr->bbr_state), sendtime);
			}
		}
	} else if ((bbr->flex8 == HYBRID_LOG_RATE_CAP) ||
		   (bbr->flex8 == HYBRID_LOG_CAP_CALC)) {
		uint64_t rate_cap, lt_bw, now, deadline;
		const char *res;
		
		deadline = bbr->cur_del_rate;
		now = l->tlb_tv.tv_sec * 1000000;
		now += l->tlb_tv.tv_usec;
		lt_bw = bbr->flex3;
		lt_bw <<= 32;
		lt_bw |= bbr->flex2;
		rate_cap = bbr->flex5;
		rate_cap <<= 32;
		rate_cap |= bbr->flex4;
		if (bbr->flex8 == HYBRID_LOG_CAP_CALC) {
			res = "CU cap calc";
		} else {
			if (bbr->pacing_gain == 0)
				res = "by catch up";
			else if (bbr->pacing_gain == 1)
				res = "hard limit";
			else if (bbr->pacing_gain == 2)
				res = "fillcw cap";
			else
				res = "unknown";
		}
		fprintf(out, "Reason:%s ts:%u capped rate wanted:%s (%lu) from %s -- ",
			hybrid_mode(bbr->flex8),
			bbr->timeStamp, 
			display_bw(bbr->bw_inuse, 0), bbr->bw_inuse,
			res);
		fprintf(out, "gp_est:%s (%lu)\n",
			display_bw(bbr->delRate, 0), bbr->delRate);
		print_out_space(out);
		fprintf(out, "  lt_bw:%s (%lu) ",
			display_bw(lt_bw, 0), lt_bw);
		fprintf(out, "  rate_cap:%s (%lu) Flags:%s\n",
			display_bw(rate_cap, 0), rate_cap, get_hybrid_pacing_flags(bbr->bbr_state));
		if (extra_print) {
			int64_t del;

			del = ((int64_t)deadline - (int64_t)now);
			print_out_space(out);
			fprintf(out, "deadline:%lu now:%lu (tim:%ld) end_seq:%u start_seq:%u snd_una:%u (left:%u) cs_mss:%u\n",
				deadline, now, del, bbr->pkts_out, bbr->flex6, l->tlb_snd_una,
				(bbr->pkts_out - l->tlb_snd_una), bbr->bbr_substate);
		}
	
	} else {
		fprintf(out, "Don't know how to render %s [%d]\n",
			hybrid_mode(bbr->flex8), bbr->flex8);	
	}
}

static void
dump_out_lro_log(const struct tcp_log_buffer *l, const struct tcp_log_bbr *bbr)
{
	if (bbr->flex8 == 22) {
		fprintf(out,
			"Frm:%d(new) cpu:%u inp_flags2:0x%x in_input:0x%x ack_seq:%u next_seq:%u comp:%u un_comp:%d win:%d\n",
			bbr->flex8,
			bbr->lost,
			bbr->inflight,
			bbr->delivered,
			ntohl(bbr->lt_epoch),
			bbr->epoch,
			bbr->flex7,
			bbr->pacing_gain,
			ntohs(bbr->cwnd_gain));
	} else if (bbr->flex8 == 23) {
		fprintf(out,
			"Frm:%d(append) cpu:%u ack_seq:%u next_seq:%u win:%u\n",
			bbr->flex8,
			bbr->lost,
			ntohl(bbr->lt_epoch),
			bbr->epoch,
			ntohs(bbr->cwnd_gain));
	} else if (bbr->flex8 == 25) {
		fprintf(out,
			"Frm:%d(can_append now false) cpu:%u tlen:%u\n",
			bbr->flex8,
			bbr->lost,
			bbr->flex1);
	} else if (bbr->flex8 == 24) {
		fprintf(out,
			"Frm:%d(added compresed with mv pp) cpu:%u tlen:%u\n",
			bbr->flex8,
			bbr->lost,
			bbr->flex1);
	} else if (bbr->flex8 == 26) {
		fprintf(out,
			"Frm:%d(added compressed no mv pp) cpu:%u tlen:%u\n",
			bbr->flex8,
			bbr->lost,
			bbr->flex1);
	} else {
		fprintf(out, "Unknown %d\n", bbr->flex8);
	}
	if (extra_print) {
		print_out_space(out);
		fprintf(out, "head_mflags:0x%lx head_arr_tstmp:0x%lx log_time:%u rcv_nxt:%u snd_una:%u\n",
			bbr->delRate,
			bbr->rttProp, bbr->flex6, l->tlb_rcv_nxt, l->tlb_snd_una);
	}
	lro_flush_time = bbr->flex6;
	if (lro_flush_is_ms)
		lro_flush_time *= 1000;

}

static uint32_t last_rwnd_at_out = 0;

static void
show_pacer_diag(const struct tcp_log_bbr *bbr)
{
	const char  *state;
	uint32_t p_lasttick, p_curtick;

	if (bbr->use_lt_bw == 0) {
		p_lasttick = (bbr->cur_del_rate & 0x00000000ffffffff);
		p_curtick = ((bbr->cur_del_rate >> 32) & 0x00000000ffffffff);
		if (bbr->flex7)
			state = "active";
		else
			state = "sleeping";
		fprintf(out, "INP %s p_hpts_active:%u nxt_slot:%u cur_slot:%u prev_slot:%u runningtick:%u\n",
			state,
			bbr->flex7,
			bbr->flex1,
			bbr->flex2,
			bbr->delivered,
			bbr->inflight);
		if (extra_print) {
			print_out_space(out);
			fprintf(out, "PACERDIAG slot_req:%u inp_hptsslot:%u slot_remaining:%u have_slept:%u\n",
				bbr->flex3, bbr->flex4, bbr->flex5, bbr->epoch);
			print_out_space(out);
			fprintf(out, "PACERDIAG hptscpu:%u actcpu:%u inp_flowid:%u inp_flowtype:%u\n",
				bbr->pacing_gain, bbr->cwnd_gain, bbr->lost, bbr->pkt_epoch);
			print_out_space(out);
			fprintf(out, "PACERDIAG hpts_sleep_time:%u yet_to_sleep:%u need_new_to:%u wheel_tick:%lu maxticks:%lu\n",
				bbr->applimited, bbr->lt_epoch, bbr->flex6,
				bbr->bw_inuse, bbr->delRate);
			print_out_space(out);
			fprintf(out, "PACERDIAG wheel_cts:%lu co_ret:%u on_min_sleep:%d ctim:%u ptim:%u (ctim - ptim = %u) (wheel - p_curtick = %u) \n",
				bbr->rttProp, bbr->pkts_out, bbr->flex8, p_curtick, p_lasttick,
				(p_curtick - p_lasttick),
				((uint32_t)bbr->rttProp - p_curtick)
				);

		}
	} else if (bbr->use_lt_bw == 1) {
		/*
		 * flex1 - contains the next slot after our run.
		 * flex2 - contains the current slot (translated time now to slot)
		 * flex3 - contains the previous slot from the last run.
		 * flex4 - contains the slot array index we are processing (i)
		 * flex5 - contains the current tick i.e. the time we started mapped to the wheel.
		 * flex6 - contains the number of inp's on the this wheel.
		 * flex7 - contains the cpu we are running on.
		 * flex8 - indicates if we are from the callout(1) or from a syscall/lro (0)
		 * inflight - tells us how many ticks we are running in this pass
		 * applimited - tells us the overriden_sleep value.
		 * delivered  - tells the saved_curtick i.e the tick on entry at the beginning.
		 * epoch - tells us the saved_curslot i.e. the curslot on entry
		 * lt_epoch - tells us the saved prev slot i.e the prevslot on entry
		 * pkts_out - tells us the calculated delayed by value
		 * lost - tells us the last calculated slot to sleep too.
		 * pacing_gain - tells us the cpu this hpts is assigned
		 * pkt_epoch - Is the tick we are currently processing.
		 * use_lt_bw - is set to 1 to indicate this type of diag log
		 */
		fprintf(out, "PACER(%s) nxt_slot:%u prev_slot:%u cur_slot:%u at:%u rt:%u onqueue:%u curtick:%u sleeptime:%u\n",
			(bbr->flex8 ? "callout" : "syscall"),
			bbr->flex1, bbr->flex3, bbr->flex2, bbr->flex4,
			bbr->pkt_epoch,
			bbr->flex6, bbr->flex5,
			bbr->lost
			);
		if (extra_print) {
			print_out_space(out);
			fprintf(out, "ticks_to_run:%u saved_prev_slot:%u saved_cur_slot:%u saved_curtick:%u delayed:%u\n",
				bbr->inflight,
				bbr->lt_epoch,
				bbr->epoch,
				bbr->delivered,
				bbr->pkts_out);
			print_out_space(out);
			fprintf(out, " sleep_override:%u actcpu:%u hptscpu:%u\n",
				bbr->applimited, bbr->flex7, bbr->pacing_gain);

		}
	} else {
		fprintf(out, "Unknown diag %d\n", bbr->use_lt_bw);
	}
}

static uint32_t cwnd_enter_time = 0;

static void
handle_sendfile_log_entry(const struct tcp_log_buffer *l)
{
	const struct tcp_log_sendfile *sf = &l->tlb_stackinfo.u_sf;
	tcp_seq start, end;

	start = l->tlb_snd_una + l->tlb_txbuf.tls_sb_acc;
	end = start + sf->length;
	fprintf(out, "offset:%" PRIu64 " len:%" PRIu64 " flags:%x [seq:%u - %u]\n",
		sf->offset, sf->length, sf->flags, start, end);
}

static uint64_t last_rxt_known = 0;
static uint64_t last_snt_known = 0;
static uint64_t pol_detection_txt = 0;
static uint64_t pol_detection_rxt = 0;


static void
show_hystart(const struct tcp_log_buffer *l, const struct tcp_log_bbr *bbr)
{
	/*
	 * Types of logs (mod value)
	 * 1 - rtt_thresh in flex1, checking to see if RTT is to great.
	 * 2 - rtt is too great, rtt_thresh in flex1.
	 * 3 - CSS is active incr in flex1
	 * 4 - A new round is beginning flex1 is round count 
	 * 5 - A new RTT measurement flex1 is the new measurement.
	 * 6 - We enter CA ssthresh is also in flex1.
	 * 7 - Socket option to change hystart executed opt.val in flex1.
	 * 8 - Back out of CSS into SS, flex1 is the css_baseline_minrtt
	 * 20 - Initial round setup
	 * 21 - Rack declares a new round.
	 */
	if (bbr->flex8 == 1) {
		fprintf(out, " -- Checking rtt:%u  thresh:%u last:%u\n",
			bbr->flex2,
			bbr->flex1,
			bbr->flex3);
	} else if (bbr->flex8 == 2) {
		fprintf(out, " -- Rtt_thresh is above the threshold current:%u (%u + %u)\n",
			bbr->flex2,
			bbr->flex3,
			bbr->flex1);
	} else if (bbr->flex8 == 3) {
		fprintf(out, " -- CSS is active increment is reduced to %u cwnd:%u\n",
			bbr->flex1, l->tlb_snd_cwnd);
	} else if (bbr->flex8 == 4) {
		fprintf(out, " -- New round begins round:%u ends:%u cwnd:%u ssthresh:%u\n",
			bbr->flex1, bbr->flex2, l->tlb_snd_cwnd, l->tlb_snd_ssthresh);
	} else if (bbr->flex8 == 5) {
		fprintf(out, " -- RTT Sample rtt:%u smallest-rtt:%u flags:0x%x cwnd:%u\n",
			bbr->flex1, bbr->flex2, bbr->flex7, l->tlb_snd_cwnd);
	} else if (bbr->flex8 == 6) {
		fprintf(out, " -- Enter CA ssthresh will be set to %u ssthresh:%u cwnd:%u\n",
			bbr->flex1, l->tlb_snd_ssthresh, l->tlb_snd_cwnd);
	} else if (bbr->flex8 == 7) {
		fprintf(out, " -- Socket option to allow/disable hystart opt:%u flags end up:0x%x\n",
			bbr->flex1, bbr->flex7);
	} else if (bbr->flex8 == 8) {
		fprintf(out, " -- RTT drops below baseline:%u new-lowrtt:%u -- back to slow-start\n",
			bbr->flex1, bbr->flex2);
	} else if (bbr->flex8 == 20) {
		fprintf(out, " -- Init round setup cur_rnd:%u ends_at:%u\n",
			bbr->flex1, bbr->flex2);
		print_out_space(out);
		fprintf(out, "snd_una:%u snd_max:%u iss:%u\n",
			l->tlb_snd_una,
			l->tlb_snd_max,
			l->tlb_iss);
	} else if (bbr->flex8 == 21) {
		double top, bot, per_oa, per_rnd, per_pd;
		
		top = bbr->delRate * 100.0;
		bot = bbr->cur_del_rate * 1.0;
		if (bot > 0.0) {
			per_oa = top / bot;
		} else {
			if (top > 0.0) {
				per_oa = 100000.0;;
			} else {
				per_oa = 0.0;
			}
		}
		top = (bbr->delRate - last_rxt_known) * 100.0;
		bot = (bbr->cur_del_rate - last_snt_known) * 1.0;
		if (bot > 0.0) {
			per_rnd = top / bot;
		} else {
			if (top > 0.0) {
				per_rnd = 100000.0;
			} else {
				per_rnd = 0.0;
			}
		}
		top = ((bbr->delRate - pol_detection_rxt)  * 100.0);
		bot = ((bbr->cur_del_rate - pol_detection_txt) * 1.0);
		if (bot > 0.0) {
			per_pd = top / bot;
		} else {
			if (top > 0.0) {
				per_pd = 100000.0;
			} else {
				per_pd = 0.0;
			}
		}
		fprintf(out, " -- NR setup r:%u (s:%lu r:%lu [%.4f]) cw:%u t_r_ (s:%lu r:%lu [%.4f]) [since_pd[%.4f]]\n",
			bbr->flex1,
			bbr->cur_del_rate,
			bbr->delRate,
			per_oa,
			l->tlb_snd_cwnd,
			(bbr->cur_del_rate - last_snt_known),
			(bbr->delRate - last_rxt_known), per_rnd, per_pd);
		print_out_space(out);
		fprintf(out, "ends_at:%u highseq:%u cur_snd_max:%u\n",
			bbr->flex2, bbr->flex3, bbr->flex4);
		last_rxt_known = bbr->delRate;
		last_snt_known = bbr->cur_del_rate;
	} else {
		fprintf(out, "Unknown flex8:%d\n", bbr->flex8);
	}
	if (extra_print && (bbr->flex8 <= 8)) {
		print_out_space(out);
		fprintf(out, "cur_min:%u last_min:%u scnt:%u e_at:%u baseline:%u flags:0x%x\n",
			bbr->flex2, bbr->flex3, bbr->flex4, bbr->flex5, bbr->flex6, bbr->flex7);
		print_out_space(out);
		fprintf(out, "cur_rnd:%u fas_at_ent:%u last_fas:%u lowfast:%u cw:%u\n",
			bbr->epoch,
			bbr->lt_epoch,
			bbr->pkts_out,
			bbr->delivered,
			l->tlb_snd_cwnd);
	}
	/*
	  Here is the logs settings...
		log.u_bbr.flex1 = flex1;
		log.u_bbr.flex2 = ccv->css_current_round_minrtt;
		log.u_bbr.flex3 = ccv->css_lastround_minrtt;
		log.u_bbr.flex4 = ccv->css_rttsample_count;
		log.u_bbr.flex5 = ccv->css_entered_at_round;
		log.u_bbr.flex6 = ccv->css_baseline_minrtt;
		log.u_bbr.flex7 = ccv->flags & 0x0000ffff;
		log.u_bbr.flex8 = mod;
		log.u_bbr.epoch = ccv->css_current_round;
		log.u_bbr.timeStamp = tcp_get_usecs(&tv);
		log.u_bbr.lt_epoch = ccv->css_fas_at_css_entry;
		log.u_bbr.pkts_out = ccv->css_last_fas;
		log.u_bbr.delivered = ccv->css_lowrtt_fas;
	*/
}

void
print_pace_size(const struct tcp_log_buffer *l, const struct tcp_log_bbr *bbr)
{
	if (bbr->flex8 == 1) {
		/* The pacing calculation from tcp_ratelimit.c */
		fprintf(out, "Size calculation bw:%s(%lu) segsiz:%u new_tso:%u\n",
			display_bw(bbr->cur_del_rate, 0),
			bbr->cur_del_rate,
			bbr->flex1, bbr->flex2);
	} else if (bbr->flex8 == 2) {
		/* Rack uses the value 2 in flex8 to announce any changes */
		fprintf(out, "Sizes Changed - Old min:%u Old max:%u min:%u max:%u line:%d sb_acc:%u\n",
			bbr->flex4, bbr->flex5,
			bbr->flex1, bbr->flex3, bbr->flex6,
			l->tlb_txbuf.tls_sb_acc);
	} else if (bbr->flex8 == 3) {
		/* Hardware pacing is involved we are possibly stepping up the tso size */
		fprintf(out, "HDWR Pacing upscale hdwr rate %s(%lu) time_bet:%u calc_bet:%u segs:%u mult:%d\n",
			display_bw(bbr->delRate, 0),
			bbr->delRate,
			bbr->flex3, bbr->flex4,
			bbr->flex5, bbr->flex7);
	} else if (bbr->flex8 == 4) {
		/* Client error, rate set is below rate desired */
		char *hw;

		hw = display_bw(bbr->cur_del_rate, 1),
		fprintf(out, "HDWR to Software rate-mismatch hdwr rate:%s(%lu) software:%s(%lu) time_bet:%u > calc_bet:%u\n",
			hw, bbr->cur_del_rate,
			display_bw(bbr->delRate, 0),
			bbr->delRate,
			bbr->flex3, bbr->flex4);
		if (hw)
			free(hw);
	} else if (bbr->flex8 == 5) {
		fprintf(out, "Hybrid pace size min:%u max:%u h_mss:%u orig_mss:%u u_s_min:%u line:%d\n",
			bbr->flex1,
			bbr->flex2,
			bbr->flex4,
			bbr->flex5,
			bbr->flex7,
			bbr->flex6);
	}
}

static void
dump_accounting(const struct tcp_log_buffer *l)
{
	int i, limit;
	const char *acct_type;

	limit = (int)l->tlb_flex1;
	if (l->tlb_flex2 == 1) {
		acct_type = "Counts";
	} else if (l->tlb_flex2 == 2) {
		acct_type = "Cycles";
	} else {
		acct_type = "Unknown?";
	}
	fprintf(out, "%s type:%s:\n", evt_name(l->tlb_eventid), acct_type);
	for (i = 0; i < limit; i++) {
		print_out_space(out);
		fprintf(out, "%s:%lu\n",
			((l->tlb_flex2 == 2) ?
			 tcp_cycle_names[i] : tcp_accounting_names[i]),
			l->tlb_stackinfo.u64_raw.u64_flex[i]);
	}
}

static void
dump_log_entry(const struct tcp_log_buffer *l, const struct tcphdr *th)
{
	const char *mask;
	uint32_t calc1, calc2;
	uint32_t time_display;
	const uint8_t *optptr;
	int id, val;
	struct tcpopt to;
	char time_shown[100];
	char sign=0, foo;
	const struct tcp_log_bbr *bbr;
	uint32_t th_ack, th_seq, sub, dif;
	struct timeval wct;
	int colat;

	id = l->tlb_eventid;
	if (id == TCP_LOG_ACCOUNTING) {
		dump_accounting(l);
		return;
	}
	is_bbr = 1;
	if ((include_user_send == 0)  &&
	    (id == TCP_LOG_USERSEND)) {
		tlb_sn = l->tlb_sn;
		return;
	}
	if (id == TCP_LOG_SOCKET_OPT) {
		sock_opt_cnt++;
	}
	if (lh != NULL) {
		if (tag_dumped == 0) {
			tag_dumped = 1;
			strcpy(log_tag, lh->tlh_tag);
		}
		wct.tv_sec = lh->tlh_offset.tv_sec + l->tlb_tv.tv_sec;
		wct.tv_usec = lh->tlh_offset.tv_usec + l->tlb_tv.tv_usec;
		while (wct.tv_usec > 1000000) {
			wct.tv_usec -= 1000000;
			wct.tv_sec++;
		}
		last_time.tv_sec = wct.tv_sec;
		last_time.tv_usec = wct.tv_usec;
	}
	if ((lh != NULL) && early_filled == 0) {
		uint32_t ticks_passed, sec, usec;

		early_filled = 1;
		earliest_time.tv_sec = wct.tv_sec;
		earliest_time.tv_usec = wct.tv_usec;
		connection_begin_time.tv_sec = earliest_time.tv_sec;
		connection_begin_time.tv_usec = earliest_time.tv_usec;
		/* Now how many ticks since we started have passed? */
		ticks_passed = l->tlb_ticks - l->tlb_starttime;
		/* Back up our earliest time by that many ticks */
		sec = ticks_passed / 1000;
		usec = ticks_passed % 1000;
		usec *= 1000;
		if (usec > earliest_time.tv_usec) {
			connection_begin_time.tv_sec--;
			connection_begin_time.tv_usec += 1000000;
		}
		connection_begin_time.tv_usec -= usec;
		connection_begin_time.tv_sec -= sec;
	}
	bbr = &l->tlb_stackinfo.u_bbr;
	if ((id != TCP_LOG_USERSEND) &&
	    (id != TCP_LOG_FLOWEND) &&
	    (id != TCP_LOG_CONNEND) &&
	    (id != TCP_LOG_SOCKET_OPT)){
		last_time_stamp = bbr->timeStamp;
		if (bbr_first_time_set == 0) {
			last_evt_time = first_time = bbr->timeStamp;
			time_saw_avail_zero = bbr->timeStamp;
			bbr_first_time_set = 1;
			if (state_is_set == 0) {
				state_is_set = 1;
				major_stateval = bbr->bbr_state;
				state_transition_time = bbr->timeStamp;
				if ((bbr->bbr_state == BBR_STATE_PROBE_BW) &&
				    (minor_is_set == 0)) {
					minor_is_set = 1;
					minor_state = bbr->bbr_substate;
					minor_state_transition_time = bbr->timeStamp;
				}
			}
		}
		if (SEQ_GT(last_evt_time, bbr->timeStamp)) {
			dif = last_evt_time - bbr->timeStamp;
			sign = '-';
		} else {
			dif = bbr->timeStamp - last_evt_time;
			sign = '+';
		}
		if (pg_not_set) {
			time_started_using_ltbw = epoch_time = last_evt_time = last_input_time = last_ack_time = last_pg_chg = bbr->timeStamp;
			last_time_stamp = bbr->timeStamp;
			timeOfAppLimit = bbr->timeStamp;
			timeOfnoAvail = bbr->timeStamp;
			timeOfnoRwnd = bbr->timeStamp;
			time_ended_using_lt_bw = bbr->timeStamp;
			pg_not_set = 0;
		}
	}
	if (tlb_sn == 0) {
		tlb_sn = l->tlb_sn - 1;
	}
	if (bbr->applimited && (is_app_limited == 0)) {
		timeOfAppLimit = bbr->timeStamp;
		is_app_limited = 1;
		app_limited_transitions++;
	} else if (is_app_limited && (bbr->applimited == 0)) {
		if (SEQ_GT(bbr->timeStamp, timeOfAppLimit)) {
			total_time_app_limited += (bbr->timeStamp - timeOfAppLimit);
		}
		is_app_limited = 0;
		app_limited_transitions++;
	}
	if (id != TCP_LOG_LRO) {
		if ((bbr->use_lt_bw) && (using_lt_bw == 0)) {
			time_started_using_ltbw = bbr->timeStamp;
			time_data_ltbw = bbr->timeStamp;
			fprintf(out, "# Started using LTBW\n");
			using_lt_bw = 1;
		} else if ((using_lt_bw) && (bbr->use_lt_bw == 0)) {
			if (TSTMP_GT(bbr->timeStamp, time_started_using_ltbw)) {
				total_time_using_lt_bw += (bbr->timeStamp - time_started_using_ltbw);
			}
			time_ended_using_lt_bw = bbr->timeStamp;
			fprintf(out, "# Stopped using LTBW\n");
			using_lt_bw = 0;
		}
	}
	if ((l->tlb_txbuf.tls_sb_acc == 0) && (is_none_avail == 0)) {
		timeOfnoAvail = bbr->timeStamp;
		is_none_avail = 1;
	} else if (is_none_avail && l->tlb_txbuf.tls_sb_acc) {
		if (SEQ_GT(bbr->timeStamp, timeOfnoAvail)) {
			total_time_no_avail += (bbr->timeStamp - timeOfnoAvail);
		}
		is_none_avail = 0;
	}
	if ((l->tlb_snd_wnd == 0) && (is_none_rwnd == 0)) {
		is_none_rwnd = 1;
		timeOfnoRwnd = bbr->timeStamp;
	} else if (is_none_rwnd && l->tlb_snd_wnd) {
		is_none_rwnd = 0;
		if (SEQ_GT(bbr->timeStamp, timeOfnoRwnd)) {
			total_time_no_rwnd += (bbr->timeStamp - timeOfnoRwnd);
		}
	}
	if (using_lt_bw == 1) {
		if (is_none_rwnd || is_none_avail) {
			/* we have none available or are presisting stop time */
			if (is_ltbw_sndok && SEQ_GT(bbr->timeStamp, time_data_ltbw)) {
				total_time_ltbw_sendok += (bbr->timeStamp - time_data_ltbw);
			}
			is_ltbw_sndok = 0;
			time_data_ltbw = bbr->timeStamp;
		} else if (is_ltbw_sndok == 0) {
			time_data_ltbw = bbr->timeStamp;
			is_ltbw_sndok = 1;
		}
	} else if (is_ltbw_sndok == 1) {
		/* We stopped */
		is_ltbw_sndok = 0;
		if (SEQ_GT(bbr->timeStamp, time_data_ltbw)) {
			total_time_ltbw_sendok += (bbr->timeStamp - time_data_ltbw);
		}
	}
	if (SEQ_GT(bbr->timeStamp, last_time_stamp)) {
		total_time_in_trace += (bbr->timeStamp - last_time_stamp);
		last_time_stamp = bbr->timeStamp;
	}
	if (policing_on && (set_pkt_epoch == 0)) {
		if (IN_RECOVERY(l->tlb_flags) == 0) {
			set_pkt_epoch = bbr->pkt_epoch;
			lost_at_thresh = bbr->lost;
			delivered_at_thresh = bbr->delivered;
		}
	}
	
	if (tlb_sn_set >  0) {
		if ((tlb_sn+1) != l->tlb_sn) {
			if (tlb_sn > l->tlb_sn) {
				duplicates++;
				fprintf(out, "\n***Roll back sn:%d -> l->tlb_sn:%d ****\n", tlb_sn, l->tlb_sn);
				goto backwards;
			} else if (show_all_messages) {
				fprintf(out, "***Missing sn:%d -> l->tlb_sn:%d ****\n", tlb_sn, l->tlb_sn);
			}
			total_missed_records += (l->tlb_sn - tlb_sn);
		}
	}
backwards:
	if (avail_is_zero) {
		if (l->tlb_txbuf.tls_sb_acc) {
			/* No longer zero */
			avail_is_zero = 0;
			time_avail_zero += (bbr->timeStamp - time_saw_avail_zero);
		}
	} else {
		if (l->tlb_txbuf.tls_sb_acc == 0) {
			time_saw_avail_zero = bbr->timeStamp;
			avail_is_zero = 1;
		}
	}
	if (bbr->use_lt_bw)
		saw_ltbw_set = 1;
	tlb_sn = l->tlb_sn;
	tlb_sn_set = 1;
	if (show_all_messages) {
		if ((id != TCP_LOG_USERSEND) &&
		    (id != TCP_LOG_SOCKET_OPT)){
			if (time_is_relative && bbr_first_time_set) {
				time_display = bbr->timeStamp - first_time;
			} else {
				if (time_is_relative && first_time_set) {
					time_display = bbr->timeStamp - first_time;
				} else {
					time_display = bbr->timeStamp;
				}
				sprintf(time_shown, "%u", time_display);
			}
		} else {
			time_display = 0;
			sprintf(time_shown, "0");
		}
		if (id == BBR_LOG_STATE) {
			do_state_accounting(bbr);
			if ((log_all_state_change == 0) && (bbr->bbr_state == 3) && (opg == bbr->pacing_gain) && (bbr->bbr_state == old_state))
				;
			else {
				fprintf(out,
					"%s %u [%c%u] %s **********************************************************************************\n",
					time_shown, number_flow, sign, dif, evt_name(id));
				if (show_record)
					fprintf(out, "|%u|%s %u [%c%u] %s ",
						l->tlb_sn, time_shown, number_flow, sign, dif, evt_name(id));
				else
					fprintf(out, "%s %u [%c%u] %s ", time_shown, number_flow, sign, dif, evt_name(id));
			}
		} else {
			if ((id != TCP_LOG_USERSEND) &&
			    (id != TCP_LOG_SOCKET_OPT)) {
				if (show_record)
					fprintf(out, "|%u|%s %u [%c%u] %s ",
						l->tlb_sn, time_shown, number_flow, sign, dif, evt_name(id));
				else
					fprintf(out, "%s %u [%c%u] %s ",  time_shown,
						number_flow, sign, dif, evt_name(id));
			} else {
				if (show_record)
					fprintf(out, "|%u|%s %u [--] %s ", l->tlb_sn,
						time_shown, number_flow, evt_name(id));
				else
					fprintf(out, "%s %u [--] %s ", time_shown, number_flow, evt_name(id));
			}
		}
	}
	if ((id != TCP_LOG_USERSEND) && (id != TCP_LOG_SOCKET_OPT))
		last_evt_time = bbr->timeStamp;

	if ((print_out_the_time) &&
	    (id != TCP_LOG_USERSEND) &&
	    (id != TCP_LOG_SOCKET_OPT)) {
		fprintf(out, " tv:%lu.%lu ",
			l->tlb_tv.tv_sec,
			l->tlb_tv.tv_usec);
	}
	switch (id) {
	case TCP_LOG_SOCKET_OPT:
		display_tcp_option(l);
		break;

	case BBR_LOG_RTT_SHRINKS:
	{
		uint32_t tim_dif;
		double secs;
		const char *reas;

		/* Flex 2 has last time we shrunk the filter */
		/* Flex 3 has last time we exited probe-rtt  */
		tim_dif = bbr->timeStamp - bbr->flex3;
		secs = (tim_dif * 1.0) / 1000000.0;
		if (bbr->flex8 < SHRINKS_LAST)
			reas = shrinks_reasons[bbr->flex8];
		else
			reas = shrinks_reasons[SHRINKS_LAST];
		if (bbr->flex8 == BBR_RTTS_RESETS_VALUES) {
			/*
			 * We are changing the RTT
			 * probe interval and filter limit.
			 */
			fprintf(out, " %s(%u) new-interval:%u filter-limit:%u mod:%d [Time Since PRTT %2.3f]\n",
				reas,
				bbr->flex1,
				bbr->flex4,
				bbr->flex5, bbr->flex7,
				secs);
		} else if ((bbr->flex8 == BBR_RTTS_SHRINK_PG) ||
			   (bbr->flex8 == BBR_RTTS_SHRINK_PG_FINAL) ||
			   (bbr->flex8 == BBR_RTTS_NEW_TARGET) ||
			   (bbr->flex8 == BBR_RTTS_ENTERPROBE) ||
			   (bbr->flex8 == BBR_RTTS_REACHTAR)) {
			/* These are all about the target */
			fprintf(out, " %s(%u) tar:%u flt:%u pg:%d [Time Since PRTT %2.3f] cw:%u\n",
				reas,
				bbr->flex1,
				bbr->flex6,
				bbr->inflight,
				bbr->pacing_gain,
				secs, l->tlb_snd_cwnd);
		} else if (bbr->flex8 == BBR_RTTS_RTTPROBE) {
			fprintf(out, " %s(%u) flt:%u pg:%u rttProp:%lu\n",
				reas, bbr->flex1,
				bbr->inflight,
				bbr->pacing_gain, bbr->rttProp);
		} else if (bbr->flex8 == BBR_RTTS_LEAVE_DRAIN) {
			fprintf(out, " %s(%u) flt:%u pg:%u [Time Since PRTT %2.3f]\n",
				reas, bbr->flex1,
				bbr->inflight,
				bbr->pacing_gain,
				secs);
		} else if ((bbr->flex8 == BBR_RTTS_PERSIST) ||
			   (bbr->flex8 == BBR_RTTS_WASIDLE)) {
			fprintf(out, " %s(%u) flt:%u pg:%u [Time Since PRTT %2.3f]\n",
				reas,bbr->flex1,
				bbr->inflight,
				bbr->pacing_gain,
				secs);
		} else if (bbr->flex8 == BBR_RTTS_INIT) {
			fprintf(out, " %s(%u) [Time Since 0.0]\n",
				reas,bbr->flex1);
		} else if (bbr->flex8 == BBR_RTTS_NEWRTT) {
			fprintf(out, " %s(%u) newrtt:%u old rttProp:%lu [Time Since PRTT %2.3f]\n",
				reas, bbr->flex1,
				bbr->flex5,
				bbr->rttProp,
				secs);
		} else {
			fprintf(out, " %s(%u) flex4:%u flex5:%u tar:%u flt:%u pg:%d [Time Since PRTT %2.3f] cw:%u\n",
				reas,
				bbr->flex1,
				bbr->flex4,
				bbr->flex5,
				bbr->flex6,
				bbr->inflight,
				bbr->pacing_gain,
				secs, l->tlb_snd_cwnd);
		}
	}
	break;
	case TCP_LOG_LRO:
		dump_out_lro_log(l, bbr);
		break;
	case BBR_LOG_TIMERPREP:
		if (bbr->flex8 == 1) {
			fprintf(out, "TLP:time-since:%u srtt:%u thresh:%u to:%u t_srtt:%u t_var:%u cw:%u\n",
				bbr->flex2, bbr->flex3, bbr->flex4, bbr->flex5, bbr->flex6, bbr->flex1, l->tlb_snd_cwnd);
		} else {
			fprintf(out, "RXT:srtt:%u to:%u t_srtt:%u t_var:%u cw:%u\n",
				bbr->flex3, bbr->flex5, bbr->flex6, bbr->flex1, l->tlb_snd_cwnd);
		}
		break;

	case BBR_LOG_LOWGAIN:
		if (show_all_messages) {
			if (bbr->flex8 == 1) {
				fprintf(out, "Collapsing seq:%u snd_una:%u snd_max:%u (out:%u rw:%u)\n",
					bbr->flex1,
					l->tlb_snd_una,
					l->tlb_snd_max,
					(l->tlb_snd_max -l->tlb_snd_una),
					l->tlb_snd_wnd);
			} else if (bbr->flex8 == 0) {
				fprintf(out, "Expanding seq:%u snd_una:%u snd_max:%u (out:%u rw:%u) unmarked:%u\n",
					bbr->flex1,
					l->tlb_snd_una,
					l->tlb_snd_max,
					(l->tlb_snd_max -l->tlb_snd_una),
					l->tlb_snd_wnd, bbr->flex2);
			} else if (bbr->flex8 == 3) {
				fprintf(out, "Splitting a segment seq:%u snd_una:%u snd_max:%u (out:%u rw:%u)\n",
					bbr->flex1,
					l->tlb_snd_una,
					l->tlb_snd_max,
					(l->tlb_snd_max -l->tlb_snd_una),
					l->tlb_snd_wnd);
			} else if (bbr->flex8 == 4) {
				fprintf(out, "Collapsing marked %u\n",
					bbr->flex2);
			}
		}
		break;
	case TCP_LOG_RTT:
		fprintf(out, " rtt:%u applied to srtt %u var %u StateTarget:%u\n",
			bbr->flex1,
			((l->tlb_srtt * 1000) >> TCP_RTT_SHIFT),
			((l->tlb_rttvar * 1000) >> TCP_RTT_SHIFT),
			bbr->flex5);
		if (extra_print) {
			print_out_space(out);
			fprintf(out, " t_flags:0x%x rttProp:%lu ack-delay:%u(f:%d) time_in_state:%u late:%d\n",
				l->tlb_flags, bbr->rttProp, bbr->flex3, bbr->flex8,
				(bbr->timeStamp - bbr->flex2), bbr->flex4);
		}
		break;
	case RACK_DSACK_HANDLING:
		printf(" -- Unexpected\n");
		break;
	case BBR_LOG_BW_RED_EV:
	{
		int idx;
		if (bbr->flex7 > 6) {
			idx = 7;
		} else
			idx = bbr->flex7;
		if (bbr->flex7 == 3) {
			fprintf(out, "in_red:%d '%s' pe:%d ex_rpe:%d lost:%u delivered:%u high_thresh:%u high_perc:%d rtpe:%d cw:%u\n",
				bbr->flex8,
				red_bw_reasons[idx],
				bbr->pkt_epoch,
				bbr->flex1,
				bbr->flex2,
				bbr->flex5,
				bbr->flex3,
				bbr->flex4, bbr->flex6, l->tlb_snd_cwnd);
		} else {
			fprintf(out, "in_red:%d '%s' pe:%d ex_rpe:%d bwm_cont_at:%d high_thresh:%d high_perc:%d rtpe:%d cw:%u\n",
				bbr->flex8,
				red_bw_reasons[idx],
				bbr->pkt_epoch,
				bbr->flex1,
				bbr->flex2,
				bbr->flex3,
				bbr->flex4, bbr->flex6, l->tlb_snd_cwnd);
		}

	}
	break;
	case BBR_LOG_HPTSDIAG:
		/*
		 * The pacer diag abuses 3 bbr fields to transfer
		 * all insert pacer information.
		 */
		if (show_all_messages) {
			show_pacer_diag(bbr);
		}
		break;
	case BBR_LOG_BBRTSO:
		if (show_all_messages) {
			if ((bbr->flex8 & 0x80) == 0)
				fprintf(out, " TSO size:%u (TLS-sz:%u) min_pacer_sleep:%u min_pace_sz:%d old:%u maxseg:%d piw:%d ug:%d\n",
					bbr->flex1,
					bbr->flex2,
					bbr->flex3,
					bbr->flex4,
					bbr->flex5,
					bbr->flex6,
					bbr->flex7,
					bbr->flex8);
			else
				fprintf(out, " HDWR TSO calc delta:%u cur_del:%u hdwr_del:%u segs:%u\n",
					bbr->flex1,
					bbr->flex2,
					bbr->flex5, bbr->flex6);
		}
		break;
	case BBR_LOG_TO_PROCESS:
		if (show_all_messages) {
			int32_t ret;

			ret = (int32_t)bbr->flex2;
			if (ret >= 0) {
				mask = get_timer_mask(bbr->flex1);
				fprintf(out, " timers %s return %d expires:%u pc:%d cw:%u\n",
					mask, bbr->flex2, bbr->flex3, bbr->flex8, l->tlb_snd_cwnd);
			} else {
				/* A early to */
				mask = get_timer_mask(bbr->flex4);
				if (ret == -1) {
					fprintf(out, "Out pacing tmr %s expires:%u pc:%u cw:%u\n",
						mask, bbr->flex3, bbr->flex8, l->tlb_snd_cwnd);
				} else if (ret == -2) {
					fprintf(out, "Not pacer calling for tmr %s pc:%u cw:%u\n",
						mask, bbr->flex8, l->tlb_snd_cwnd);
				} else {
					fprintf(out, "Not enough time yet tmr %s left:%d reinsert cts:%u exp:%u pc:%u cw:%u\n",
						mask, bbr->flex1, bbr->flex5, bbr->flex3, bbr->flex8, l->tlb_snd_cwnd);
				}
			}
			if (extra_print) {
				print_out_space(out);
				fprintf(out, "tv %lu.%6.6lu ticks:%u cts:%u\n",
					l->tlb_tv.tv_sec, l->tlb_tv.tv_usec, l->tlb_ticks, bbr->timeStamp);
			}
		}
		break;
	case BBR_LOG_TIME_EPOCH:
	{
		double perc, chg, base, lossr;
		if (del_rate < bbr->delRate) {
			sign = '+';
			chg = (bbr->delRate - del_rate) * 1.0;
		} else {
			sign = '-';
			chg = (del_rate - bbr->delRate) * 1.0;
		}
		base = pe_btlbw * 1.0;
		perc = (100.0 * chg) / base;
		if ((bbr->delivered-epoch_delivered) && bbr->lost) {
			lossr = ((double)(bbr->lost-epoch_lost) * 100.0)/((double)(bbr->delivered-epoch_delivered) * 1.0);
		} else {
			lossr = 0.0;
		}
		if (show_all_messages) {
			if (bbr->use_lt_bw) {
				fprintf(out, " Old:%u New:%u in %u usecs, LTBW:%ld rttProp:%ld flight:%u cw:%u rw:%u\n",
					epoch, bbr->epoch, (bbr->timeStamp - epoch_time),
					bbr->bw_inuse, bbr->rttProp, bbr->inflight,
					l->tlb_snd_cwnd, l->tlb_snd_wnd);
			} else {
				fprintf(out, "Old:%u New:%u in %u usecs, DR:%s rttProp:%ld flight:%u cw:%u rw:%u\n",
					epoch, bbr->epoch, (bbr->timeStamp - epoch_time),
					display_bw(bbr->delRate, 0),
					bbr->rttProp, bbr->inflight,
					l->tlb_snd_cwnd, l->tlb_snd_wnd);
			}
			if (extra_print) {
				uint64_t lesser, greater;
				print_out_space(out);
				fprintf(out, "EPOCH_TIME avail:%u [%c%2.2f%%] lost:%u del:%u [lr:%2.3f] line:%u\n",
					l->tlb_txbuf.tls_sb_acc, sign, perc,
					(bbr->lost-epoch_lost), (bbr->delivered-epoch_delivered), lossr, bbr->flex7);
				print_out_space(out);

				if ((bbr->flex5 + bbr->flex6) > 0) {
					lesser = bbr->flex5;
					lesser *= 10000;
					lesser /= (bbr->flex5 + (uint64_t)bbr->flex6);
				} else
					lesser = 0;

				if ((bbr->flex2 + bbr->flex3) > 0) {
					greater = bbr->flex2;
					greater *= 10000;
					greater /= (bbr->flex2 + (uint64_t)bbr->flex3);
				} else
					greater = 0;
				fprintf(out, "EPOCH_TIME lost-gt:%u del-gt:%u [%lu] tim_g:%u lost-lt:%u del-lt:%u [%lu] tim_l:%u hot:%d\n",
					bbr->flex2, bbr->flex3, greater, bbr->flex4,
					bbr->flex5, bbr->flex6, lesser, bbr->applimited, bbr->flex8);
				print_out_space(out);
				fprintf(out, "Low_water:%u High_water:%u\n",
					bbr->flex2, bbr->flex3);
			}
		}
		epoch = bbr->epoch;
		epoch_lost = bbr->lost;
		epoch_delivered = bbr->delivered;
		epoch_time = bbr->timeStamp;
		del_rate = bbr->delRate;
	}
	break;
	case  TCP_LOG_USERSEND:
		if (show_all_messages) {
			fprintf(out, "avail:%u pending:%u snd_una:%u snd_max:%u out:%u t_flags:0x%x\n",
				l->tlb_txbuf.tls_sb_acc,
				l->tlb_txbuf.tls_sb_ccc,
				l->tlb_snd_una,
				l->tlb_snd_max,
				(l->tlb_snd_max - l->tlb_snd_una),
				l->tlb_flags);
		}
		break;
	case TCP_LOG_SENDFILE:
		if (show_all_messages) {
			handle_sendfile_log_entry(l);
		}
		break;
	case BBR_LOG_THRESH_CALC:
		if (show_all_messages) {
			if (bbr->flex8 == BBR_TO_FRM_RACK) {
				fprintf(out, "Thresh:%u lro:%u reorder_ts:%u sent:%u t_currxt:%u srttu:%u roshif:%d\n",
					bbr->flex1,
					bbr->flex2,
					bbr->flex3,
					bbr->flex4,
					bbr->flex5,
					bbr->flex6,
					bbr->flex7);
			} else if (bbr->flex8 == BBR_TO_FRM_TLP) {
				fprintf(out, "TLP threshold calc\n");
			} else {
				fprintf(out, "Unknown threshold calc %d\n", bbr->flex8);
			}

		}
		break;
	case BBR_LOG_EXIT_GAIN:
		if (show_all_messages) {
			int eidx;
			const char *reas_name=NULL;
			const char *ename[6] = {
				"Enter Probe RTT",
				"Exit Probe RTT",
				"Gain reaches target",
				"Drain reaches target",
				"Drain reduces pg",
				"Unknown"
			};
			eidx = bbr->flex8;
			if (eidx >= 5)
				eidx  = 5;
			reas_name = ename[eidx];
			fprintf(out, " %s DR:%s pg:%d target:%u flight:%u gain_to_now:%u pe:%u\n",
				reas_name,
				display_bw(bbr->delRate, 0),
				bbr->pacing_gain,
				bbr->flex1,
				bbr->inflight,
				(bbr->timeStamp - bbr->flex3),
				bbr->pkt_epoch);
			if (extra_print) {
				print_out_space(out);
				fprintf(out, "state_at_flight:%u now:%u snd_w:%u epoch:%d lost:%u tso:%u\n",
					bbr->flex6,
					bbr->timeStamp,
					bbr->epoch,
					l->tlb_snd_wnd,
					bbr->lost,
					bbr->flex4);
			}
		}
		break;
	case TCP_LOG_FLOWEND:
		if (show_all_messages) {
			fprintf(out, " --- Flow ends delivered:%u lost:%u epoch:%u pkt-epoch:%u\n",
				bbr->delivered, bbr->lost, bbr->epoch,  bbr->pkt_epoch);
		}
		break;
	case BBR_LOG_PERSIST:
		if (show_all_messages) {
			fprintf(out, " %s persists (value:%d) line:%d", (bbr->flex8 ? "Enter" : "Exit"), bbr->flex8,
				bbr->flex2);
			if (bbr->flex8)
				fprintf(out, "\n");
			else {
				fprintf(out, " Was in persists for %u useconds\n", bbr->flex1);
				total_time_persisting += bbr->flex1;
			}
		} else {
			if (bbr->flex8) {
				fprintf(out, "# Entering persists mode -- state changes stopped\n");
			} else {
				fprintf(out, "# Exiting persists mode -- state changes begin again\n");
			}
		}
		break;
	case BBR_LOG_PROGRESS:
		fprintf(out, " line:%d ticks:%u ack_time:%u max:%u event:%s\n",
			bbr->flex1,
			bbr->flex2,
			bbr->flex3,
			bbr->flex4,
			get_progress_event(bbr->flex8));
		break;
	case BBR_LOG_HPTSI_CALC:
	{
		char *bws;
		uint64_t a, b, c;
		b = bbr->flex3;
		c = bbr->flex4;
		a = (b << 32);
		a |= c;
		if (a)
			bws = display_bw(a, 1);
		else
			bws = NULL;
		fprintf(out, "mod:%d bw:%s(%lu) len/off:%u gain:%u -> usecs:%u (used %s:%lu ohr:0x%x)\n",
			bbr->flex8,
			display_bw(bbr->delRate, 0), bbr->delRate,
			bbr->flex2,
			bbr->flex7,
			bbr->flex1, ((bws == NULL) ? "0.0" : bws), a, bbr->flex5);
		if (bws)
			free(bws);
		if (extra_print) {
			/* Assume hz = 1000 */
			print_out_space(out);
			fprintf(out, "tv %lu.%6.6lu ticks:%u cts:%u cw:%u over:%u srtt:%u var:%u rw:%u cw:%u out:%u\n",
				l->tlb_tv.tv_sec, l->tlb_tv.tv_usec, l->tlb_ticks, bbr->timeStamp, l->tlb_snd_cwnd,
				bbr->flex6, ((l->tlb_srtt * 1000) >> TCP_RTT_SHIFT), ((l->tlb_rttvar * 1000) >> TCP_RTT_SHIFT),
				l->tlb_snd_wnd, l->tlb_snd_cwnd, (l->tlb_snd_max - l->tlb_snd_una));
		}
	}
	break;
	case BBR_LOG_ENOBUF_JMP:
		fprintf(out, " line:%d len:%d orig_len:%u cwnd:%u rw:%u avail:%u segcnt:%d segsiz:%u\n",
			bbr->flex1,
			l->tlb_len,
			bbr->flex2,
			l->tlb_snd_cwnd,
			l->tlb_snd_wnd,
			l->tlb_txbuf.tls_sb_acc,
			bbr->flex3,
			bbr->flex4
			);
		break;
	case TCP_SACK_FILTER_RES:
		dump_sack_filter(bbr);
		break;
	case BBR_LOG_DOSEG_DONE:
		if (show_all_messages) {
			char *bw_str;
			uint32_t chg;

			if (last_rwnd_at_out > l->tlb_snd_wnd) {
				sign = '-';
				chg = last_rwnd_at_out - l->tlb_snd_wnd;
			} else if (last_rwnd_at_out == l->tlb_snd_wnd) {
				sign = ' ';
				chg = 0;
			} else {
				sign = '+';
				chg = l->tlb_snd_wnd - last_rwnd_at_out;
			}
			bw_str = display_bw(bbr->delRate, 1);
			if (bbr->flex4)
				mask = get_timer_mask(bbr->flex4);
			else
				mask = "NONE";
			fprintf(out, "DR:%s cDR:%s do:%d np:%d wo:%d in_per:%d tmrs:%s(0x%x) cw:%u rw:%u (%c%u) flt:%u\n",
				bw_str,
				display_bw(bbr->cur_del_rate, 0),
				bbr->flex1,
				bbr->flex2,
				bbr->flex7,
				bbr->flex8,
				mask,
				bbr->flex4,
				l->tlb_snd_cwnd,
				l->tlb_snd_wnd,
				sign, chg,
				bbr->inflight);
			if (extra_print) {
				print_out_space(out);
				fprintf(out, "flags:0x%x appl:%u del:%u rw:%u lost:%u tmr:%u lb:%u (ip:%d pe:%d lt:%d)\n",
					l->tlb_flags, bbr->applimited, bbr->delivered, l->tlb_snd_wnd, bbr->lost,
					bbr->flex5, bbr->flex6,
					bbr->inhpts, bbr->pkt_epoch, bbr->use_lt_bw);

			}
			if (bw_str)
				free(bw_str);
		}
		break;
	case BBR_LOG_PKT_EPOCH:
		if (show_all_messages) {
			double perc, chg, base;
			char *dr, *cdr;
			uint64_t mul;

			if (pe_btlbw < bbr->delRate) {
				sign = '+';
				chg = (bbr->delRate - pe_btlbw) * 1.0;
			} else {
				sign = '-';
				chg = (pe_btlbw - bbr->delRate) * 1.0;
			}
			base = pe_btlbw * 1.0;
			perc = (100.0 * chg) / base;
			cdr = display_bw(bbr->cur_del_rate, 1);
			dr = display_bw(bbr->delRate, 1);
			if ((bbr->flex2 + bbr->flex1) > 0) {
				mul = bbr->flex1 * 10000;
				mul /= (bbr->flex2 + bbr->flex1);
			} else
				mul = 0;
			fprintf(out, " e:%u pe:%u d:%d del:%u lost:%u (td:%u tl:%u))(%lu) from line:%d ep_rtt:%u DR:%s cDR:%s mc:%u [%c%3.2f%%]\n",
				bbr->epoch,
				bbr->pkt_epoch,
				bbr->flex8,
				bbr->flex2,
				bbr->flex1,
				bbr->delivered, bbr->lost,
				mul,
				bbr->flex7,
				(bbr->timeStamp - prev_pkt_epoch), /* delta */
				dr, cdr, bbr->inflight,
				sign,
				perc);
			if (extra_print) {
				print_out_space(out);
				print_epoch_loss(bbr->pkt_epoch, bbr->lost, bbr->delivered);
			}
			if (cdr)
				free(cdr);
			if (dr)
				free(dr);
		}
		prev_pkt_epoch = bbr->timeStamp;
		pe_btlbw = bbr->delRate;
		break;
	case BBR_LOG_SETTINGS_CHG:
	{
		double delta;

		if (last_set_set)
			delta = (bbr->timeStamp - time_last_setting) / 1000000.0;
		else
			delta = 0.0;
		fprintf(out, "divisor (R-HU):%x, gain_dr:%d hot_en:%d reduce:%d New:%d Old:%d (time of old %3.3f seconds)\n",
			bbr->flex1,
			bbr->flex2,
			bbr->flex3,
			bbr->flex4,
			bbr->flex8,
			bbr->flex7, delta);
		if (last_set_set  == 0)
			last_set_set = 1;
		time_last_setting = bbr->timeStamp;
	}
	break;
	case TCP_LOG_REQ_T:
		tcp_display_http_log(l, bbr);
		break;
	case TCP_LOG_SB_WAKE:
		tcp_display_wakeup(l, bbr);
		break;
	case TCP_HYSTART:
		show_hystart(l, bbr);
		break;
	case TCP_LOG_RTO:
		display_tcp_rto(l);
		break;
	case TCP_LOG_IN:
	{
		int off_len;
		uint32_t tasf;
		const char *ackflags;
		uint32_t acks, snd_una;
		int have_ack;

		last_rwnd_at_out = l->tlb_snd_wnd;
		snd_una = l->tlb_snd_una;
		if (th) {
			ackflags = translate_flags(tcp_get_flags(th));
			have_ack = th->th_flags & TH_ACK;
			th_ack = ntohl(th->th_ack);
			th_seq = ntohl(th->th_seq);
			if (irs_set == 0) {
				irs = th_seq;
				irs_set = 1;
			}
			if (use_relative_seq) {
				th_seq -= irs;
				th_ack -= l->tlb_iss;
				snd_una -= l->tlb_iss;
			}
			off_len = th->th_off << 2;
			tasf = th_ack - l->tlb_iss;
		} else {
			ackflags = "UNK";
			have_ack = 0;
			off_len = 0;
			th_ack = 0xbadbad;
			th_seq = 0xbadbad;
			tasf = 0;
		}
		sub = bbr->timeStamp - last_ack_time;
		last_spa_seen = sub;
		last_ack_time = bbr->timeStamp;
		if (have_ack && SEQ_GT(th_ack, snd_una)) {
			acks = th_ack - snd_una;
		} else {
			acks = 0;
		}
		if (show_all_messages) {
			fprintf(out, "Acks %u (%s:%u) [Nsegs:%d] off:%d out:%u len_in:%u avail:%u cw:%u rw:%u ts:%d (spa:%u ip:%d ack:%u) st:%u loss:%u\n",
				acks,
				ackflags, th_ack,
				bbr->flex1,
				off_len,
				(l->tlb_snd_max - l->tlb_snd_una),
				l->tlb_len,
				l->tlb_txbuf.tls_sb_acc,
				l->tlb_snd_cwnd,
				l->tlb_snd_wnd,
				l->tlb_state,
				sub, bbr->inhpts, th_ack, bbr->flex4, bbr->lost);
			if (extra_print) {
				uint64_t prec_tstmp;
				uint64_t sec, usec;

				prec_tstmp = bbr->flex5;
				prec_tstmp <<= 32;
				prec_tstmp |= bbr->flex6;
				sec = prec_tstmp / 1000000000;
				usec = (prec_tstmp % 1000000000) / 1000;
				if (prec_tstmp) {
					uint32_t usec_ts, ts_delta;

					usec_ts = (sec * HPTS_USEC_IN_SEC) + usec;
					print_out_space(out);
					ts_delta = bbr->timeStamp - usec_ts;
					if (ts_delta < lowest_delta)
						lowest_delta = ts_delta;
					if (ts_delta > highest_delta)
						highest_delta = ts_delta;
					fprintf(out, "prec-tstmp:0x%lx sec:%lu usec:%lu convert:%u (del:%u)\n",
						prec_tstmp,
						sec, usec,
						usec_ts, ts_delta);

				}
				print_out_space(out);
				fprintf(out, "rcv_buf cc:%u snd_buf cc:%u m_flags:0x%x mss:%u\n",
					l->tlb_rxbuf.tls_sb_acc, l->tlb_txbuf.tls_sb_acc, bbr->flex3, bbr->pkts_out);
				print_out_space(out);
				fprintf(out, " snd_una:%u th_ack:%u pe:%u th_seq:%u rcv_nxt:%u tasf:%u srtt_red:%u\n",
					snd_una, th_ack, bbr->pkt_epoch, th_seq, l->tlb_rcv_nxt, tasf,
					bbr->flex6);
				print_out_space(out);
				if (bbr->flex3 & M_TSTMP) {
					fprintf(out, " m_flags:0x%x hdwr_arrtstmp:%u(%d) flush_time:%u lb:%u\n",
						bbr->flex3,
						bbr->lt_epoch, (bbr->timeStamp - bbr->lt_epoch),
						bbr->flex6,
						bbr->flex2);
				} else if (bbr->flex3 & M_TSTMP_LRO) {
					fprintf(out, " m_flags:0x%x lro_arrtstmp:%u(%d) flush_time:%u lb:%u\n",
						bbr->flex3,
						bbr->flex5, (bbr->timeStamp - bbr->flex5),
						bbr->flex6,
						bbr->flex2);
				} else {
					fprintf(out, "  No hdwr or lro timestamp flush_time:%u?\n",
						bbr->flex6);
				}
				optptr = (const uint8_t *)th;
				optptr += sizeof(struct tcphdr);
				process_options(&to, th, optptr);
				if (to.to_flags & TOF_TS) {
					print_out_space(out);
					fprintf(out, "TSTMP VAL:%u ECHO:%u TICKS:%u\n",
						to.to_tsval, to.to_tsecr, l->tlb_ticks);
				}
				if (to.to_flags & TOF_SACK) {
					print_sack_blocks(&to, th_ack);
				} else {
					if (dump_out_sack) {
						print_out_space(out);
						fprintf(dump_out_sack, "ACK:%u\n", th_ack);
						print_out_space(out);
						fprintf(dump_out_sack, "DONE\n");
					}
				}
			}
		}
		if (th && (th->th_flags & TH_RST) && (ann_end == 0)) {
			ann_end = 1;
			fprintf(out, "***Flow Ends sent %u bytes\n", (l->tlb_snd_max - l->tlb_iss));
		}
		break;
	}
	case BBR_LOG_REDUCE:	/* Hijacked old reduce is startup log */
	{
		const char *pstr;
		if (bbr->flex8 > 11)
			pstr = startup_reasons[0];
		else
			pstr = startup_reasons[bbr->flex8];
		fprintf(out,
			"%s pe:%u flex4:%u flex1:%u flex2:%u (lost tot:%u) gain flex3:%u oldbttlbw:%lu Dr:%lu st:%u\n",
			pstr,
			bbr->pkt_epoch,
			bbr->flex4,
			bbr->flex1,
			bbr->flex2,
			bbr->lost,
			bbr->flex3, bbr->cur_del_rate,
			bbr->delRate, bbr->flex5);
	}
	break;
	case TCP_LOG_REASS:
		print_tcp_log_reass(l, bbr);
	case BBR_LOG_HDWR_PACE:
	{
		uint64_t hw_bw;
		uint64_t ptr;
		char *bwd, *hw_bwd, *req_bwd;
		bwd = display_bw(bbr->delRate, 1);
		req_bwd = display_bw(bbr->bw_inuse, 1);
		hw_bw = bbr->flex1;
		hw_bw <<= 32;
		hw_bw |= bbr->flex2;
		hw_bwd = display_bw(hw_bw, 1);

		ptr = bbr->flex3;
		ptr <<= 32;
		ptr |= bbr->flex4;
		fprintf(out,
			"Line:%d ifp:0x%lx err:%d (DR:%s req_BW:%s hw_bw:%s) SGH:0x%x\n",
			bbr->flex5,
			ptr, bbr->flex6,
			bwd, req_bwd, hw_bwd,
			bbr->flex8);
		if (bwd)
			free(bwd);
		if (req_bwd)
			free(req_bwd);
		if (hw_bwd)
			free(hw_bwd);
	}
	break;
	case TCP_HDWR_PACE_SIZE:
		print_pace_size(l, bbr);
		break;
	case BBR_LOG_TSTMP_VAL:
		fprintf(out, "ratio:%u use_it:%d set:%d peer_delta:0x%x%x delta:0x%x%x\n",
			bbr->flex1,
			bbr->flex8,
			bbr->flex7,
			bbr->flex2, bbr->flex3,
			bbr->flex4, bbr->flex5);
		break;
	case TCP_LOG_CONNEND:
		display_connection_end(l, bbr);
		break;
	case BBR_LOG_STATE_TARGET:
		fprintf(out, "old:%u new:%u from line %d meth:%d quanta:%u tso:%u mss:%u (msscnt:%u)\n",
			bbr->flex1, bbr->flex2, bbr->flex3, bbr->flex8,
			bbr->flex5, bbr->flex4, (bbr->flex6 - bbr->flex7),
			(bbr->flex2/(bbr->flex6 - bbr->flex7)));
		break;
	case TCP_CHG_QUERY:
		display_change_query(l, bbr);
		break;
	case TCP_RACK_TP_TRIGGERED:
		display_tp_trigger(l);
		break;
	case TCP_HYBRID_PACING_LOG:
		display_hybrid_pacing(l, bbr);
		break;
	case TCP_LOG_PRU:
		display_pru(l);
		break;
	case TCP_LOG_OUT:
	{
		const char *bwd;
		int sidx;
		int drain, t_maxseg;
		uint64_t bwo;
		uint8_t piw, pacing_dis, filled;


		if (bbr->flex5 & 0x80000000)
			filled = 1;
		else
			filled = 0;
		if (bbr->flex5 & 0x40000000)
			piw = 1;
		else
			piw = 0;
		if (bbr->flex5 & 0x20000000)
			pacing_dis = 1;
		else
			pacing_dis = 0;
		t_maxseg = bbr->flex5 & 0x00ffffff;
		drain = (bbr->flex2 >> 2) & 0x1;
		bwd = display_bw(bbr->bw_inuse, 0);
		bwo = bbr->bw_inuse;
		if (bbr->bbr_state == 3) {
			sidx = bbr->bbr_substate;
		} else {
			sidx = 8;
		}
		if (th) {
			th_ack = ntohl(th->th_ack);
			th_seq = ntohl(th->th_seq);
			if (use_relative_seq) {
				th_seq -= l->tlb_iss;
			}
		} else {
			th_ack = 0xbadbad;
			th_seq = 0xbadbad;
		}
		sent_state[sidx] += l->tlb_len;
		if ((bbr->flex8 == 1) || (bbr->flex8 == 2)) {
			retran_count += l->tlb_len;
			if (bbr->flex8 == 1)
				foo = '*';
			else
				foo = 'T';
		} else if (bbr->flex8 == 4) {
			foo = 'R';
		} else {
			foo = ' ';
		}
		state_send_count++;
		state_send_bytes += l->tlb_len;
		sub = bbr->timeStamp - last_out_time;
		last_out_time = bbr->timeStamp;
		if (show_all_messages) {
			fprintf(out, "Sent(e:%d) %u:%u%c (%s:%d) flt:%u avail:%d (spo:%u ip:%d rdhu:0x%x %s(%lu) pg:%u piw:%d pd:%d d:%d)\n",
				l->tlb_errno,
				th_seq, l->tlb_len, foo,
				translate_flags(tcp_get_flags(th)), l->tlb_errno,
				bbr->inflight,
				l->tlb_txbuf.tls_sb_acc,
				sub, bbr->inhpts,
				bbr->flex2, bwd, bwo, bbr->pacing_gain, piw, pacing_dis, drain);
			if (extra_print) {
				uint32_t low, high;

				bwd = display_bw(bbr->delRate, 0);
				bwo = bbr->delRate;
				print_out_space(out);
				fprintf(out, "cw:%u rw:%u filled:%d pe:%u delay:%u tso:%u agg_delay:%u maxseg:%u t_maxseg:%u DR:%s(%lu)\n",
					l->tlb_snd_cwnd,
					l->tlb_snd_wnd,
					filled,
					bbr->epoch,
					bbr->flex4,
					bbr->flex6, bbr->flex1,
					bbr->flex3, t_maxseg, bwd, bwo);
				print_out_space(out);
				low = bbr->rttProp & 0x00000000ffffffff;
				high = (bbr->rttProp >> 32);
				fprintf(out, "tv %lu.%6.6lu ticks:%u cts:%u lrtt:%u hrtt:%u (%u) flex5:0x%x\n",
					l->tlb_tv.tv_sec, l->tlb_tv.tv_usec, l->tlb_ticks,
					bbr->timeStamp, low, high, (high - low), bbr->flex5);
				print_out_space(out);
				fprintf(out, "DR:%lu cDR:%lu uBW:%lu appl_limited:%u delivered:%u\n",
					bbr->delRate,
					bbr->cur_del_rate,
					bbr->bw_inuse, bbr->applimited, bbr->delivered);
				optptr = (const uint8_t *)th;
				optptr += sizeof(struct tcphdr);
				process_options(&to, th, optptr);
				if (to.to_flags & TOF_TS) {
					print_out_space(out);
					fprintf(out, "TSTMP VAL:%u ECHO:%u\n",
						to.to_tsval, to.to_tsecr);
				}
				if (to.to_flags & TOF_SACK) {
					print_sack_blocks(&to, th_ack);
				} else {
					if (dump_out_sack) {
						print_out_space(out);
						fprintf(dump_out_sack, "ACK:%u\n", th_ack);
						print_out_space(out);
						fprintf(dump_out_sack, "DONE\n");
					}
				}
			}
		}
		if (th && (th->th_flags & TH_FIN) && (ann_end == 0)) {
			ann_end = 1;
			fprintf(out, "***Flow Ends sent %u bytes\n", (l->tlb_snd_max - l->tlb_iss));
		}
		break;
	}
	case BBR_LOG_RTO:
		val = bbr->flex8;
		if (val > 6)
			val = 0;
		if (show_all_messages) {
			fprintf(out, "Type:%s expires set_to:%u at line:%d (ip:%d) out:%u cw:%u rw:%u pe:%u srtt:%u\n",
				timer_types[val],
				bbr->flex2,
				bbr->flex1,
				bbr->inhpts,
				(l->tlb_snd_max - l->tlb_snd_una),
				l->tlb_snd_cwnd,
				l->tlb_snd_wnd, bbr->pkt_epoch, ((l->tlb_srtt*1000) >> TCP_RTT_SHIFT));
			if (val == 1) {
				uint64_t rto;

				rto = ((l->tlb_srtt  + (l->tlb_rttvar * 4)) * 1000);
				rto >>= TCP_RTT_SHIFT;
				fprintf(out, "       RTO timer is srtt:%u rttvar:%u rto:%luus\n",
					l->tlb_srtt, l->tlb_rttvar, rto);


			}
		}
		if ((dump_out_sack) && (val == 1)) {
			fprintf(dump_out_sack, "RXT\n");
		}
		break;
	case TCP_LOG_PRR:
	case TCP_LOG_REORDER:
	case TCP_LOG_HPTS:
		if (show_all_messages)
			fprintf(out, "\n");
		break;
	case BBR_LOG_BBRUPD:
		if (show_all_messages) {
			char *bw_str, *cur_del_rate_str;
			bw_str = display_bw(bbr->delRate, 1);
			/*
			 * BBRUPD Map
			 * bbr_log_type_bbrupd(struct tcp_bbr *bbr, uint8_t flex8, uint32_t cts,
			 * uint32_t flex3, uint32_t flex2, uint32_t flex5,
			 * uint32_t flex6, uint32_t pkts_out, int flex7,
			 * uint32_t flex4, uint32_ flex1)
			 *
			 */
			cur_del_rate_str = display_bw(bbr->cur_del_rate, 1);
			if (bbr->flex8 == 1) {
				/* Part one of rate structure */
				fprintf(out, "App:1 s:%u e:%u (%u) fs:%u ls:%u (se:%u) fsca:%u\n",
					bbr->flex1, bbr->flex2,
					(bbr->flex2-bbr->flex1),
					bbr->flex3, bbr->flex4, (bbr->flex4 - bbr->flex3),
					bbr->inflight);
				print_out_space(out);
				fprintf(out, "App:1 fa:%u la:%u (ae:%u) del:%u idx:%d used:%d open:%u\n",
					bbr->flex5, bbr->flex6,  (bbr->flex6 - bbr->flex5), bbr->delivered,
					bbr->flex7, bbr->epoch, bbr->applimited);
			} else if (bbr->flex8 == 2) {
				/* Part two of rate structure */
				int64_t p_d_s, p_d_t;

				p_d_s = bbr->flex3;
				p_d_s <<= 32;
				p_d_s |= bbr->flex4;
				p_d_t = bbr->flex5;
				p_d_t <<= 32;
				p_d_t |= bbr->flex6;
				fprintf(out, "App:2 p_m_lrtt:%u p_m_lrtt_st:%u pds:%ld pdt:%ld\n",
					bbr->flex1,
					bbr->flex2, p_d_s, p_d_t);
				print_out_space(out);
				fprintf(out, "App:2 ack_cnt:%d rtt1:%d rtt2:%d rtt3:%d rtt4:%d\n",
					bbr->flex7,
					bbr->applimited,
					bbr->delivered,
					bbr->pkts_out,
					bbr->epoch);
			} else if (bbr->flex8 == 3) {
				fprintf(out, "App:3 ack_cnt:%d a %s more rtt's\n",
					bbr->flex7, (bbr->flex7 <= 4) ? "no" : "herd");
			} else if (bbr->flex8 == 4) {
				uint8_t bflag, aflag;
				uint16_t from_idx;

				from_idx = bbr->flex4 & 0x0000ffff;
				aflag = (bbr->flex4 >> 16) & 0x000000ff;
				bflag = (bbr->flex4 >> 24) & 0x000000ff;
				fprintf(out,
					"App:4 Copied tail del:%u frm_idx:%d bflag:0x%x aflag:%x to_idx:%u first_ack:%u end:%u fabyt:%u\n",
					bbr->flex3, from_idx, bflag, aflag,
					bbr->flex7, bbr->pkts_out, bbr->flex2, bbr->flex5);

/*			bbr_log_type_bbrupd(bbr, 4, cts,
			rt->al_delivered,
			rt->r_seq_end, rt->al_seq_start,
			__LINE__, nxt->al_first_ack, nxt->r_index, before_flags, nxt->al_first_send_time);
*/
			} else if (bbr->flex8 == 5) {
				const char *reason_str;
				/*
				 * BBRUPD Map
				 * bbr_log_type_bbrupd(struct tcp_bbr *bbr, uint8_t flex8, uint32_t cts,
				 * uint32_t flex3, uint32_t flex2, uint32_t flex5,
				 * uint32_t flex6, uint32_t pkts_out, int flex7,
				 * uint32_t flex4, uint32_ flex1)
				 *
				 */
				if (bbr->pkts_out == 0)
					reason_str = "limited";
				else if (bbr->pkts_out == 1)
					reason_str = "not past f-a";
				else if (bbr->pkts_out == 2)
					reason_str = "Not compressed";
				else
					reason_str = "unknown?";
				fprintf(out, "App:5 ack-line %s ss:%u se:%u (%u)"
					"del:%u ackcnt:%u pe_s:%u pe:%u (%u) Line:%u\n",
					reason_str,
					bbr->flex1, bbr->flex2,
					(bbr->flex2 - bbr->flex1),
					bbr->flex3, bbr->flex7, bbr->flex5,
					bbr->pkt_epoch,
					(bbr->pkt_epoch - bbr->flex5),
					bbr->flex6);
			} else if ((bbr->flex8 == 7) ||
				   (bbr->flex8 == 8) ||
				   (bbr->flex8 == 6)){
				/*
				 * BBRUPD Map
				 * bbr_log_type_bbrupd(struct tcp_bbr *bbr, uint8_t flex8, uint32_t cts,
				 * uint32_t flex3, uint32_t flex2, uint32_t flex5,
				 * uint32_t flex6, uint32_t pkts_out, int flex7,
				 * uint32_t flex4, uint32_ flex1)
				 *
				 */
				uint64_t bw_ovr;
				bw_ovr = bbr->flex5;
				bw_ovr <<= 32;
				bw_ovr |= bbr->flex6;
				fprintf(out, "App:%d del:%u tim:%u (bwo:%s) flex4:%u flex1:%u pkts_out(fts):%u\n",
					bbr->flex8,
					bbr->flex3, bbr->flex2,
					display_bw(bw_ovr,0), bbr->flex4, bbr->flex1, bbr->pkts_out);
			} else if (bbr->flex8 == 9) {
				/* Ready */
				fprintf(out, "App:%d Ready idx:%d rs:%u re:%u (%u) at:%u flgs:%x al_del:%u\n",
 					bbr->flex8, /* app */
					bbr->flex7, /* index */
					bbr->flex2,
					bbr->flex5,
					(bbr->flex5 - bbr->flex2),
					bbr->flex1,
					bbr->flex4, bbr->pkts_out
					);
			} else if (bbr->flex8 == 10) {
				/* Measurement made */
				/*
				 * BBRUPD Map
				 * bbr_log_type_bbrupd(struct tcp_bbr *bbr, uint8_t flex8, uint32_t cts,
				 * uint32_t flex3, uint32_t flex2, uint32_t flex5,
				 * uint32_t flex6, uint32_t pkts_out, int flex7,
				 * uint32_t flex4, uint32_ flex1)
				 *
				 */
				fprintf(out, "App:%d idx:%d DR:%s cDR:%s(%lu) bwiu:%lu del:%u tim:%u pe:%d rsm_delt:%u rc_del_time:%u\n",
					bbr->flex8,
					bbr->flex7,
					bw_str,
					cur_del_rate_str,
					bbr->cur_del_rate,
					bbr->bw_inuse,
					bbr->flex2, bbr->flex3,
					bbr->pkt_epoch,
					bbr->flex4, bbr->flex1);
				if (extra_print) {
					print_out_space(out);
					fprintf(out, " BBRUPD avail:%u flight:%d  pg:%d cg:%d\n",
						l->tlb_txbuf.tls_sb_acc, bbr->inflight,
						bbr->pacing_gain, bbr->cwnd_gain);
				}
			} else if (bbr->flex8 == 11) {
				/* Measurement started (opened) */
				fprintf(out, "App:%d DR:%s avail:%u flight:%d pe:%d Open idx:%d seqstart:%u rs:%u re:%u flgs:%x ot:%u\n",
					bbr->flex8,
					bw_str,
					l->tlb_txbuf.tls_sb_acc, bbr->inflight, bbr->pkt_epoch,
					bbr->flex7,
					bbr->flex2, bbr->flex3, bbr->flex5,
					bbr->flex4, bbr->flex6);
			} else if (bbr->flex8 == 12) {
				/* Measurement capped */
				fprintf(out, "App:%d DR:%s avail:%u flight:%d pe:%d Capped idx:%d rs:%u re:%u (%u) hr:%d%d flg:0x%x a_del:%u\n",
					bbr->flex8,
					bw_str,
					l->tlb_txbuf.tls_sb_acc,
					bbr->inflight, bbr->pkt_epoch,
					bbr->flex7,
					bbr->flex2, bbr->flex5,
					(bbr->flex5 - bbr->flex2),
					bbr->flex4, bbr->flex6, bbr->flex4, bbr->flex1);
			} else if (bbr->flex8 == 13) {
				/* Compressed ack detection */
				fprintf(out, "App:13 reason:%d factor:%u hptsi:%u high:%u low:%u\n",
					bbr->flex3, bbr->flex2, bbr->flex5,
					bbr->flex1, bbr->flex4);
			} else if (bbr->flex8 == 14) {
				fprintf(out, "App:%d DR:%s avail:%u flight:%d pe:%d Expand idx:%d seqstart:%u rs:%u re:%u hr:%d%d flgs:0x%x a_del:%u\n",
					bbr->flex8,
					bw_str,
					l->tlb_txbuf.tls_sb_acc, bbr->inflight, bbr->pkt_epoch,
					bbr->flex7,
					bbr->flex2, bbr->flex3, bbr->flex5,
					bbr->flex6, bbr->pkts_out, bbr->flex1, bbr->flex4);
			} else if (bbr->flex8 == 16) {
				/*
				 * BBRUPD Map
				 * bbr_log_type_bbrupd(struct tcp_bbr *bbr, uint8_t flex8, uint32_t cts,
				 * uint32_t flex3, uint32_t flex2, uint32_t flex5,
				 * uint32_t flex6, uint32_t pkts_out, int flex7,
				 * uint32_t flex4, uint32_ flex1)
				 *
				 */
				fprintf(out,
					"App:16 Set ackdel high:%u low:%u (ohigh:%u olow:%u) mss:%d sad:%u bytes:%u delta:%u\n",
					bbr->flex1, bbr->flex4, bbr->flex7, bbr->pkts_out,
					bbr->flex2, bbr->flex5, bbr->flex3, bbr->flex6);
			} else if ((bbr->flex8 == 17) || (bbr->flex8 == 18)) {
				/* Abandoned measurement */
				fprintf(out, "App:%d avail:%u flight:%d pe:%d Abanondoned idx:%d seqs:%u ends:%u (%d) hot:%d red:%d\n",
					bbr->flex8,
					l->tlb_txbuf.tls_sb_acc, bbr->inflight, bbr->pkt_epoch,
					bbr->flex7,
					bbr->flex2, bbr->flex5, ((int32_t)bbr->flex5 - (int32_t)bbr->flex2), bbr->flex6, bbr->pkts_out);
			} else if (bbr->flex8 == 19) {
				fprintf(out, "App:19 idx:%d  Transit to Capped line:%d s:%u e:%u (%d) flgs:%x\n",
					bbr->flex7,
					bbr->flex1,
					bbr->flex3, bbr->flex2,
					(bbr->flex2 - bbr->flex3),
					bbr->flex5);
			} else if (bbr->flex8 == 20) {
				fprintf(out, "App:20 - Not applied CDR:%s (%lu) DR:%s (%lu)\n",
					cur_del_rate_str,
					bbr->cur_del_rate,
					bw_str,
					bbr->delRate);
			} else if (bbr->flex8 == 21) {
				fprintf(out, "App:21 - Applied CDR:%s (%lu) DR:%s (%lu) orig:%u new:%u\n",
					cur_del_rate_str,
					bbr->cur_del_rate,
					bw_str,
					bbr->delRate,
					bbr->flex3, bbr->flex2);
			} else if (bbr->flex8 == 22) {
				fprintf(out, "App:22 - Hardware pacing max rate applies %s (%lu) reduced:%u\n",
					bw_str,
					bbr->delRate,
					bbr->flex3);
			} else if (bbr->flex8 == 40) {
				/*
				 * BBRUPD Map
				 * bbr_log_type_bbrupd(struct tcp_bbr *bbr, uint8_t flex8, uint32_t cts,
				 * uint32_t flex3, uint32_t flex2, uint32_t flex5,
				 * uint32_t flex6, uint32_t pkts_out, int flex7,
				 * uint32_t flex4, uint32_ flex1)
				 *
				 */
				fprintf(out,
					"App:40 del:%u tim:%u frtt:%u lrtt:%u inter_rtt_delta:%d snd_e:%u ack_e:%u\n",
					bbr->flex3, bbr->flex2,
					bbr->flex5, bbr->flex6,
					(int32_t)bbr->pkts_out,
					bbr->flex4, bbr->flex1);
			} else if (bbr->flex8 == 42) {
				uint64_t bw;
				bw = bbr->flex4;
				bw <<= 32;
				bw |= bbr->flex1;
				fprintf(out, "App:42 Google measurement %s (%ld)",
					display_bw(bw, 0), bw);
				if (bbr->flex7 == 1) {
					fprintf(out, " was applied as %s (%ld)\n",
						display_bw(bbr->cur_del_rate, 0), bbr->cur_del_rate);
				} else {
					fprintf(out, " was not applied\n");
				}
			} else if (bbr->flex8 == 44) {
				fprintf(out, "App:44 Inter-ack skip:%d bytes:%u maxseg:%u ingain:%d indrain:%d pe:%d\n",
					bbr->flex1, bbr->flex2, bbr->flex3, bbr->flex4, bbr->flex5, bbr->pkt_epoch);
			} else if (bbr->flex8 == 50) {
				/*
				 * BBRUPD Map
				 * bbr_log_type_bbrupd(struct tcp_bbr *bbr, uint8_t flex8, uint32_t cts,
				 * uint32_t flex3, uint32_t flex2, uint32_t flex5,
				 * uint32_t flex6, uint32_t pkts_out, int flex7,
				 * uint32_t flex4, uint32_ flex1)
				 *
				 */
				fprintf(out,
					"App:50 snd_elapsed zero del:%u tim:%u frtt:%u lrtt:%u lst:%u fst::%u\n",
					bbr->flex3, bbr->flex2,
					bbr->flex5, bbr->flex6,
					bbr->flex4, bbr->flex1);
			} else if (bbr->flex8 == 51) {
				/*
				 * BBRUPD Map
				 * bbr_log_type_bbrupd(struct tcp_bbr *bbr, uint8_t flex8, uint32_t cts,
				 * uint32_t flex3, uint32_t flex2, uint32_t flex5,
				 * uint32_t flex6, uint32_t pkts_out, int flex7,
				 * uint32_t flex4, uint32_ flex1)
				 *
				 */
				fprintf(out,
					"App:51 ack_elapsed zero del:%u tim:%u frtt:%u lrtt:%u la:%u fa::%u\n",
					bbr->flex3, bbr->flex2,
					bbr->flex5, bbr->flex6,
					bbr->flex4, bbr->flex1);
			} else if (bbr->flex8 == 52) {
				fprintf(out,
					"App:52 discount equal del:%u tim:%u frtt:%u lrtt:%u la:%u fa::%u\n",
					bbr->flex3, bbr->flex2,
					bbr->flex5, bbr->flex6,
					bbr->flex4, bbr->flex1);

			} else if (bbr->flex8 == 53) {
				fprintf(out,
					"App:53 negative b/w del:%u tim:%u frtt:%u lrtt:%u la:%u fa::%u tx_ops:%d\n",
					bbr->flex3, bbr->flex2,
					bbr->flex5, bbr->flex6,
					bbr->flex4, bbr->flex1, (int32_t)bbr->pkts_out);
			} else if ((bbr->flex8 == 54) || (bbr->flex8 == 55)) {
				fprintf(out,
					"App:%d b/w %s set del:%u tim:%u dsumrtt:%u cbw:%u la:%u fa::%u tx_ops:%u\n",
					bbr->flex8,
					((bbr->flex8 == 54) ?
					 "No gradient set" : "deltasum 0"),
					bbr->flex3, bbr->flex2,
					bbr->flex5, bbr->flex6,
					bbr->flex4, bbr->flex1, bbr->pkts_out);

			} else if (bbr->flex8 == 61) {
				/*
				 * BBRUPD Map
				 * bbr_log_type_bbrupd(struct tcp_bbr *bbr, uint8_t flex8, uint32_t cts,
				 * uint32_t flex3, uint32_t flex2, uint32_t flex5,
				 * uint32_t flex6, uint32_t pkts_out, int flex7,
				 * uint32_t flex4, uint32_ flex1)
				 *
				 */
				fprintf(out, "App:61 Tsdiff invalid %u\n",
					bbr->flex3);
			} else if (bbr->flex8 == 62) {
				uint64_t tsbw;

				tsbw = bbr->flex3;
				tsbw <<= 32;
				tsbw |= bbr->flex2;
				fprintf(out, "App:62 TS b/w calculation %s (%lu)",
					display_bw(tsbw, 0), tsbw);
				fprintf(out, " calc:%s (%lu) del:%u tim:%u\n",
					display_bw(bbr->cur_del_rate, 0), bbr->cur_del_rate, bbr->flex1, bbr->flex4);
			} else if (bbr->flex8 == 63) {
				uint64_t tsbw;
				/*
				 * BBRUPD Map
				 * bbr_log_type_bbrupd(struct tcp_bbr *bbr, uint8_t flex8, uint32_t cts,
				 * uint32_t flex3, uint32_t flex2, uint32_t flex5,
				 * uint32_t flex6, uint32_t pkts_out, int flex7,
				 * uint32_t flex4, uint32_ flex1)
				 *
				 */

				tsbw = bbr->flex3;
				tsbw <<= 32;
				tsbw |= bbr->flex2;
				fprintf(out, "App:63 TS b/w calculation %s (%lu)",
					display_bw(tsbw, 0), tsbw);
				fprintf(out, " calc:%s (%lu) tim:%u del:%u last_ts:%u first_ts:%u\n",
					display_bw(bbr->cur_del_rate, 0), bbr->cur_del_rate, bbr->flex1, bbr->flex4,
					bbr->flex5, bbr->flex6);

			} else if (bbr->flex8 == 99) {
				fprintf(out, "App:99 (del:%u tim:%u) tim:%u < low_rtt:%u\n",
					bbr->flex2,
					bbr->flex3,
					bbr->flex5,
					bbr->flex6);
		        } else {
				/* ?? */
				fprintf(out, "App?:%d DR:%s cDR:%s lt:%lu del:%u tim:%u (ip:%d ult:%d) avail:%u\n",
					bbr->flex8,
					bw_str,
					cur_del_rate_str,
					bbr->bw_inuse,
					(bbr->delivered - bbr->flex6),
					(bbr->timeStamp - bbr->flex5),
					bbr->inhpts, bbr->use_lt_bw,
					l->tlb_txbuf.tls_sb_acc);
				if (extra_print) {
					print_out_space(out);
					fprintf(out, " [seq:%u:%u] e:%d al:%u pe:%u\n",
						bbr->flex3, l->tlb_len,
						bbr->epoch, bbr->applimited,
						bbr->pkt_epoch);
					print_out_space(out);
					fprintf(out, "ack_r_tim:%u send_r_tim:%u (rsm_send_t:%u old_rsm_send_t:%u)\n",
						(bbr->flex1 - bbr->flex5),
						(bbr->flex2 - bbr->inflight), bbr->flex2, bbr->inflight);
				}
			}
			free(bw_str);
			free(cur_del_rate_str);
		}
		break;
	case BBR_LOG_BBRSND:
		if (show_all_messages) {
			fprintf(out, "DR:%s ltbw:%lu rttProp:%ld sent:%u pacing_slot:%u out:%u flight:%u cw:%u line:%d (ip:%d ult:%d)\n",
				display_bw(bbr->delRate, 0),
				bbr->bw_inuse,
				bbr->rttProp,
				l->tlb_len,
				bbr->flex1,
				(l->tlb_snd_max - l->tlb_snd_una),
				bbr->inflight,
				l->tlb_snd_cwnd, bbr->flex4,
				bbr->inhpts, bbr->use_lt_bw);
			if (warn_behind) {
				if (bbr->flex6 > warn_behind)
					fprintf(stderr, "Warning behind_cnt:%u at timestamp:%u\n",
						bbr->flex6,
						time_display);
			}
			if (extra_print) {
				print_out_space(out);
				if (bbr->flex7)
					mask = get_timer_mask(bbr->flex7);
				else
					mask = "NONE";
				fprintf(out, "pe:%u delby:%u pdly:%u ldel_val:%u agg_d:%u avail:%u tmrs:%s out:%d cw:%d rw:%d state:%d\n",
					bbr->pkt_epoch,
					bbr->flex2, bbr->flex3, bbr->flex5, bbr->flex6,
					l->tlb_txbuf.tls_sb_acc,
					mask,
					(l->tlb_snd_max - l->tlb_snd_una),
					l->tlb_snd_cwnd,
					l->tlb_snd_wnd,
					l->tlb_state
					);
				print_out_space(out);
				fprintf(out, "applimited:%u delivered:%u\n",
					bbr->applimited, bbr->delivered);
			}
		}
		break;
	case BBR_LOG_ACKCLEAR:
		if (show_all_messages)
			fprintf(out, "Avail:%u cw:%u rw:%u (ip:%d ult:%d) rttProp:%ld %u st:%u\n",
				l->tlb_txbuf.tls_sb_acc,
				l->tlb_snd_cwnd,
				l->tlb_snd_wnd,
				bbr->inhpts,
				bbr->use_lt_bw,
				bbr->rttProp, bbr->pkt_epoch,
				bbr->flex5);
		if (dump_out_sack) {
			fprintf(dump_out_sack, "EXIT\n");
		}
		break;
	case BBR_LOG_INQUEUE:
		assert(bbr->bbr_state < 6);
		if (show_all_messages) {
			fprintf(out, "avail:%u cw:%u rw:%u (ip:%d ult:%d) pe:%u cpu:%d nseg:%d p_cpu:0x%x\n",
				l->tlb_txbuf.tls_sb_acc,
				l->tlb_snd_cwnd,
				l->tlb_snd_wnd,
				bbr->inhpts, bbr->use_lt_bw,
				bbr->pkt_epoch,
				bbr->flex2,
				bbr->flex1,
				bbr->flex3);
			if (extra_print) {
				print_out_space(out);
				fprintf(out, "p_icpu:%x set:%x pr:%d\n",
					bbr->flex4,
					bbr->flex5, bbr->flex6);
			}
		}
		break;
	case BBR_LOG_TIMERSTAR:
		if (show_all_messages) {
			const char *which_one;

			mask = get_timer_mask(bbr->flex3);
			if (bbr->flex8) {
				which_one = "pacer";
			} else {
				which_one =  "timer";
			}
			fprintf(out, "type:%s(%s) lineno:%d for %u(%u)  cw:%u pg:%d cg:%d pe:%u del:%u lost:%u f2:0x%x\n",
				mask,
				which_one,
				bbr->flex1,
				bbr->flex2, bbr->flex4, l->tlb_snd_cwnd, bbr->pacing_gain, bbr->cwnd_gain,
				bbr->pkt_epoch, bbr->delivered, bbr->lost, bbr->pkts_out);
			if (extra_print) {
				uint32_t calc_trxt;

				print_out_space(out);
				fprintf(out, "srtt:%u rttvar:%u rtt_shift:%d (u:%u m:%u a:%u o:%u)\n",
					((l->tlb_srtt * 1000) >> TCP_RTT_SHIFT), l->tlb_rttvar, TCP_RTT_SHIFT,
					l->tlb_snd_una,
					l->tlb_snd_max,
					l->tlb_txbuf.tls_sb_acc,
					(l->tlb_snd_max - l->tlb_snd_una));
				print_out_space(out);
				calc_trxt = (uint32_t)(((l->tlb_srtt*1000) + (l->tlb_rttvar*1000) * (uint64_t)4) >> TCP_RTT_SHIFT);
				fprintf(out, "(ip:%d ult:%d) rc:%d minto:%d t_rxtcur:%u(%u)\n",
					bbr->inhpts, bbr->use_lt_bw, bbr->flex4, bbr->flex5, bbr->flex6, calc_trxt);
				print_out_space(out);
				fprintf(out, "tv %lu.%6.6lu ticks:%u cts:%u\n",
					l->tlb_tv.tv_sec, l->tlb_tv.tv_usec, l->tlb_ticks, bbr->timeStamp);
			}
		}
		break;
	case BBR_LOG_TIMERCANC:
		mask = get_timer_mask(bbr->flex3);
		if (show_all_messages) {
			fprintf(out, "type:%s lineno:%d for %u usecs cw:%u e:%u pe:%u bbr_state:%d-%d st:%u\n",
				mask,
				bbr->flex1,
				bbr->flex2, l->tlb_snd_cwnd,
				bbr->epoch, bbr->pkt_epoch,
				bbr->bbr_state,
				bbr->bbr_substate, bbr->flex5);
			if (extra_print) {
				print_out_space(out);
				fprintf(out, " tp_flags:0x%x (ip:%d ult:%d) rm_frm_pacer:%d\n",  l->tlb_flags,
					bbr->inhpts, bbr->use_lt_bw, bbr->flex8);
				print_out_space(out);
				fprintf(out, "tv %lu.%6.6lu ticks:%u cts:%u\n",
					l->tlb_tv.tv_sec, l->tlb_tv.tv_usec, l->tlb_ticks, bbr->timeStamp);
			}
		}
		break;
	case BBR_LOG_ENTREC:
		if (show_all_messages) {
			double lr;
			if (bbr->lost == 0)
				lr = 0.0;
			else if (bbr->delivered == 0)
				lr = 100.0;
			else
				lr = (bbr->lost * 100.0)/(bbr->delivered * 1.0);
			fprintf(out, "cw:%u ocw:%u rw:%u seq:%u flags:0x%x LOSS_RATE:%2.1f%% cDR:%s flight:%u\n",
				l->tlb_snd_cwnd,
				bbr->flex2,
				l->tlb_snd_wnd,
				bbr->flex1,
				l->tlb_flags,
				lr,
				display_bw(bbr->cur_del_rate, 0), bbr->inflight);
			if (extra_print) {
				print_out_space(out);
				fprintf(out, "pe:%u  bbr_state:%d-%d\n", bbr->pkt_epoch,
					bbr->bbr_state, bbr->bbr_substate);
			}
		}
		break;
	case BBR_LOG_EXITREC:
		if (show_all_messages)
			fprintf(out, "held-cw:%u re:%u e:%u flags:0x%x out:%u cw:%u rw:%u snduna:%u sndmax:%u pe:%u st:%u\n",
				bbr->flex2,
				bbr->flex1,
				bbr->epoch,
				l->tlb_flags,
				(l->tlb_snd_max - l->tlb_snd_una),
				l->tlb_snd_cwnd,
				l->tlb_snd_wnd,
				l->tlb_snd_una,
				l->tlb_snd_max, bbr->pkt_epoch,
				bbr->flex5);
		break;
	case BBR_LOG_CWND:
		if (show_all_messages) {
			if (bbr->flex8 == 21) {
				fprintf(out, "meth:21 - cw:%u red_div:%d/%d ratio:%d rttProp:%lu E-LOSS_RATE:%u redpe:%u pe:%u flt:%u\n",
					l->tlb_snd_cwnd,
					bbr->flex3, bbr->flex4,
					bbr->flex6,
					bbr->rttProp,
					bbr->flex2,
					bbr->flex5,
					bbr->pkt_epoch, bbr->inflight);
			} else if (bbr->flex8 == 22) {
				double srtt_ratio;
				srtt_ratio = (100.0 * bbr->rttProp);
				srtt_ratio /= (1.0 * bbr->flex5);
				fprintf(out, "meth:22 - cw:%u red_div:%u/%u c-LOSS_RATE:%u srtt:%u [%2.1f%%] pe:%u lost:%u del:%d\n",
					l->tlb_snd_cwnd,
					bbr->flex3,bbr->flex4,
					bbr->flex6,
					bbr->flex5, srtt_ratio,
					bbr->pkt_epoch, bbr->lost, bbr->delivered);
			} else if (bbr->flex8 == 10) {
				fprintf(out, "meth:10 - cw:%u flight:%u vs sf:%u losses:%u\n",
					l->tlb_snd_cwnd,
					bbr->inflight,
					bbr->flex3,
					bbr->flex2);
			} else if (bbr->flex8 != 44) {
				fprintf(out, "meth:%u cw:%u bta:%u sack-chg:%u prev_ack:%u line:%d tcw:%u cwg:%u\n",
					bbr->flex8,
					l->tlb_snd_cwnd,
					bbr->flex3,
					bbr->flex4,
					bbr->flex2,
					bbr->flex1,
					bbr->flex6,
					bbr->cwnd_gain);
				if (extra_print) {
					print_out_space(out);
					fprintf(out, "th_ack:%u outstanding:%u flight:%u pe:%u cw:%d\n",
						bbr->flex5,
						(l->tlb_snd_max - l->tlb_snd_una),
						bbr->inflight, bbr->pkt_epoch, l->tlb_snd_cwnd);
				}
			} else {
				fprintf(out, "meth:%u line:%u low_rtt:%u high_rtt:%u h-l-d:%u cwnd_raw:%u target:%u\n",
					bbr->flex8,
					bbr->flex1,
					bbr->flex2,
					bbr->flex3,
					bbr->flex4,
					bbr->flex5,
					bbr->flex6);
			}
		}
		if (extra_print) {
			if (bbr->flex8 == 14) {
				/* enter recovery and save cwnd */
				cwnd_enter_time = bbr->timeStamp;
			} else if (bbr->flex8 == 15) {
				/* Exit recovery and restore cwnd */
				print_out_space(out);
				fprintf(out, "LOG_CWND:Recovery lasts %u useconds\n",
					(bbr->timeStamp - cwnd_enter_time));
				cwnd_enter_time = 0;
			} else if (bbr->flex8 == 1) {
				/* Packet conservation */
				print_out_space(out);
				fprintf(out, "LOG_CWND:Packet conservation %u useconds into recovery\n",
					(bbr->timeStamp - cwnd_enter_time));
			} else if (cwnd_enter_time &&
				   ((bbr->flex8 == 3) ||
				    (bbr->flex8 == 2) ||
				    (bbr->flex8 == 4))) {
				print_out_space(out);
				fprintf(out, "LOG_CWND:Normal cwnd update during recovery %u in\n",
					(bbr->timeStamp - cwnd_enter_time));
			}
		}
		break;
	case BBR_LOG_BWSAMP:
	{
		uint32_t del_to, lost_to;
		double top, bot, perc;
		char *ltbws;

		val = bbr->flex1;
		if (val >= REASON_MAX) {
			val = REASON_MAX-1;
		}
		lost_to = bbr->lost - bbr->flex5;
		del_to = bbr->delivered - bbr->flex6;
		if (del_to) {
			top = lost_to * 100.0;
			bot = del_to * 1.0;
			perc = top / bot;
		} else {
			perc = 0.0;
		}
		ltbws = display_bw(bbr->bw_inuse, 1);
		if (show_all_messages) {
			if (val != 6)
				fprintf(out, "%s lt_bw:%lu ltbw:%s DR:%s lt_e:%u lost:%u del:%u e:%u pe:%u alu:%u (l2:%u d2:%u loss-per:%2.3f)\n",
					lt_bw_reasons[val],
					bbr->bw_inuse,
					ltbws,
					display_bw(bbr->delRate, 0),
					bbr->lt_epoch,
					bbr->lost,
					bbr->delivered,
					bbr->epoch,
					bbr->pkt_epoch,
					bbr->applimited,
					lost_to, del_to, perc);
			else
				fprintf(out, "%s lt_bw:%lu ltbw:%s DR:%s pe:%u lt_e:%u l-del:%u l-lost:%u l-tim:%u loss-per:%2.3f\n",
					lt_bw_reasons[val],
					bbr->bw_inuse,
					ltbws,
					display_bw(bbr->delRate, 0),
					bbr->pkt_epoch,
					bbr->lt_epoch,
					bbr->flex2, bbr->flex3, bbr->pkts_out, perc);
			if (extra_print) {
				print_out_space(out);
				fprintf(out, "plost:%u pdel:%u (del:%u tim:%u) \n",
					bbr->flex5,
					bbr->flex6,
					(bbr->delivered - bbr->flex6),
					bbr->pkts_out);
			}
		}
		if (ltbws)
			free(ltbws);
	}
	break;
	case BBR_LOG_MSGSIZE:
		fprintf(out, "tso:%d maxseg:%u mtu:%u csum_flags:0x%x cw:%u rw:%u avail:%u flight:%d\n",
			bbr->flex1,
			bbr->flex2,
			bbr->flex3,
			bbr->flex4,
			l->tlb_snd_cwnd,
			l->tlb_snd_wnd,
			l->tlb_txbuf.tls_sb_acc,
			bbr->inflight
			);
		break;
	case BBR_RSM_CLEARED:
		fprintf(out, "s:%u e:%u del:%u rtr:%d snd:%d flg:0x%x oflg:0x%x line:%d\n",
			bbr->flex2, bbr->flex3,
			bbr->flex4, bbr->flex5,
			bbr->flex6, bbr->flex8,
			bbr->applimited, bbr->flex1
			);
		break;
	case BBR_LOG_BBRRTT:
		if (show_all_messages)
			fprintf(out, "Method %d rttProp:%ld smallts:%u tsin:%u rtt:%u rsm-seq:%u flag:%u pe:%u del:%u cw:%u\n",
				bbr->flex7,
				bbr->rttProp,
				bbr->flex3,
				bbr->flex4,
				bbr->flex6,
				bbr->flex5,
				bbr->flex8,
				bbr->pkt_epoch,
				bbr->delivered,
				l->tlb_snd_cwnd);
		if ((unsigned int)bbr->flex6 > (unsigned int)max_rtt_in_state) {
			max_rtt_in_state = bbr->flex6;
		}
		if ((unsigned int)bbr->flex6 < (unsigned int)min_rtt_in_state) {
			min_rtt_in_state = bbr->flex6;
		}
		break;
	case BBR_LOG_JUSTRET:
		if (show_all_messages) {
			const char *reascode;
			reascode = get_jr_reason(bbr->flex4);
			fprintf(out, "out_from_line:%u rec:%d prtt:%d tot_len:%u p_maxseg:%u cw:%u rw:%u flight:%u out:%u avail:%u (ip:%d ult:%d pc:%u) %s\n",
				bbr->pkts_out,
				((l->tlb_flags & (TF_FASTRECOVERY|TF_CONGRECOVERY)) ? 1 : 0), /* rec */
				((bbr->bbr_state == 4) ? 1 : 0),
				l->tlb_len,
				bbr->flex1,
				l->tlb_snd_cwnd,
				l->tlb_snd_wnd,
				bbr->inflight,
				(l->tlb_snd_max - l->tlb_snd_una),
				l->tlb_txbuf.tls_sb_acc,
				bbr->inhpts, bbr->use_lt_bw, bbr->flex7, reascode);
			if (extra_print) {
				mask = get_timer_mask(bbr->flex2);
				if (mask == NULL) {
					mask = "NONE";
				}
				print_out_space(out);
				fprintf(out, "pe:%u in_persist:%d state:%d from:%d tmrs:%s t_flags:0x%x len:%u\n",
					bbr->pkt_epoch, bbr->flex8,
					l->tlb_state, bbr->flex2, mask,
					l->tlb_flags, bbr->applimited);
			}
		}

		break;
	case BBR_LOG_STATE:
		assert(bbr->bbr_state < 6);
		if ((show_all_messages == 1) && (log_all_state_change == 0) && (bbr->bbr_state == 3) && (opg == bbr->pacing_gain) && (bbr->bbr_state == old_state)) {
			break;
		}
		calc1 = bbr->delivered - del_at_state;
		calc2 = bbr->lost - lost_at_state;
		if (show_all_messages) {
			uint32_t stayed, late = 0;

			if (avail_is_zero) {
				time_avail_zero += (bbr->timeStamp - time_saw_avail_zero);
				time_saw_avail_zero  = bbr->timeStamp;
			}
			if (opg < 256) {
				under_256 += (bbr->timeStamp - last_pg_chg);
				if (old_state == BBR_STATE_DRAIN)
					under_drain += (bbr->timeStamp - last_pg_chg);
				else if (old_state == BBR_STATE_PROBE_RTT)
					under_rtt += (bbr->timeStamp - last_pg_chg);
				else
					under_subdr += (bbr->timeStamp - last_pg_chg);
			} else if (opg == 256) {
				at_256 += (bbr->timeStamp - last_pg_chg);
			} else {
				over_256 += (bbr->timeStamp - last_pg_chg);
			}
			/*
			 * Now check state info
			 */
			stayed = ((bbr->timeStamp - last_pg_chg) - (uint32_t)time_avail_zero);
			if ((last_major_state == BBR_STATE_PROBE_BW) &&
			    (last_minor_state > BBR_SUB_DRAIN)) {
				if ((stayed > bbr->rttProp) &&
				    ((stayed - last_spa_seen) > bbr->rttProp)) {
					late = 1;
				}
			}
			fprintf(out, "bbrstate:%s:[%d] opg:%d -> pg:%d stayed:%u[az:%lu ltbw:%d] usecs DR:%s rttProp:%ld flight:%u st:%u srtt:%u wlate:%d\n",
				major_state[bbr->bbr_state],
				bbr->bbr_substate,
				opg, bbr->pacing_gain,
				stayed,
				time_avail_zero,
				saw_ltbw_set,
				display_bw(bbr->delRate,0),
				bbr->rttProp,
				bbr->inflight,
				bbr->pkts_out,
				((l->tlb_srtt*1000) >> TCP_RTT_SHIFT), late);
			time_avail_zero = 0;
			saw_ltbw_set = 0;
			if (extra_print) {
				char *cdr;
				char *ltbw;
				cdr = display_bw(bbr->cur_del_rate, 1);
				ltbw = display_bw(bbr->bw_inuse, 1);
				print_out_space(out);
				fprintf(out, "cw:%u rw:%u e:%u pe:%u line:%d flight:%u cdr:%s ltbw:%s\n",
					l->tlb_snd_cwnd,
					l->tlb_snd_wnd,
					bbr->epoch, bbr->pkt_epoch, bbr->flex1,
					bbr->inflight, cdr, ltbw);
				if (cdr)
					free(cdr);
				if (ltbw)
					free(ltbw);
				print_out_space(out);
				fprintf(out, "rtt_probe_lim:%u das:%u las:%u ssc:%u ssb:%u ult:%d lse:%u las:%u\n",
					bbr->flex3,
					calc1, calc2, state_send_count, state_send_bytes,
					bbr->use_lt_bw,
					bbr->flex5, bbr->flex6 );
				print_out_space(out);
				fprintf(out, "cyct:%u extra_time:%u tar:%u lost:%u\n",
					bbr->flex4, bbr->lt_epoch,
					(bbr->flex7 * 1000), bbr->lost);

			}
			fprintf(out,
				"%s %u [%c%u] %s **********************************************************************************\n",
				time_shown, number_flow, sign, dif, evt_name(id));
		} else {
			uint32_t target_cwnd;
			uint32_t gain;

			gain = bbr->cwnd_gain;
			target_cwnd = bbr_get_target_cwnd((bbr->use_lt_bw ? bbr->bw_inuse : bbr->delRate), bbr->rttProp, gain);
			if ((out_count % 50) == 0) {
				fprintf(out, "#\n");
				colat = 0;
				colat += fprintf(out, "#TIME");
				colat += pad_out(colat, 11);
				colat += fprintf(out, "STA");
				colat += pad_out(colat, 15);
				colat += fprintf(out, "TIM IS");
				colat += pad_out(colat, 24);
				colat += fprintf(out, "DR/BW");
				colat += pad_out(colat, 34);
				colat += fprintf(out, "rttProp");
				colat += pad_out(colat, 44);
				colat += fprintf(out, "minRTT");
				colat += pad_out(colat, 52);
				colat += fprintf(out, "maxRTT");
				colat += pad_out(colat, 60);
				colat += fprintf(out, "flight");
				colat += pad_out(colat, 68);
				colat += fprintf(out, "cwnd");
				colat += pad_out(colat, 76);
				colat += fprintf(out, "rwnd");
				colat += pad_out(colat, 84);
				colat += fprintf(out, "avail");
				colat += pad_out(colat, 92);
				colat += fprintf(out, "target cw");
				colat += pad_out(colat, 104);
				colat += fprintf(out, "alu");
				colat += pad_out(colat, 111);
				colat += fprintf(out, "Del is");
				colat += pad_out(colat, 119);
				colat += fprintf(out, "lost is");
				colat += pad_out(colat, 127);
				colat += fprintf(out, "snd op");
				colat += pad_out(colat, 135);
				colat += fprintf(out, "snd bytes\n");
				fprintf(out, "#\n");
			}
			colat = 0;
			colat += fprintf(out, "%u", bbr->timeStamp);
			colat += pad_out(colat, 11);
			colat += fprintf(out, "%u", state_at);
			colat += pad_out(colat, 15);
			colat += fprintf(out, "%u", (bbr->timeStamp - last_pg_chg));
			colat += pad_out(colat, 24);
			colat += fprintf(out, "%lu", (bbr->use_lt_bw ? bbr->bw_inuse : bbr->delRate));
			colat += pad_out(colat, 34);
			colat += fprintf(out, "%ld", bbr->rttProp);
			colat += pad_out(colat, 44);
			colat += fprintf(out, "%d", min_rtt_in_state);
			colat += pad_out(colat, 52);
			colat += fprintf(out, "%d", max_rtt_in_state);
			colat += pad_out(colat, 60);
			colat += fprintf(out, "%u", bbr->inflight);
			colat += pad_out(colat, 68);
			colat += fprintf(out, "%u", l->tlb_snd_cwnd);
			colat += pad_out(colat, 76);
			colat += fprintf(out, "%u", l->tlb_snd_wnd);
			colat += pad_out(colat, 84);
			colat += fprintf(out, "%u", l->tlb_txbuf.tls_sb_acc);
			colat += pad_out(colat, 92);
			colat += fprintf(out, "%u", target_cwnd);
			colat += pad_out(colat, 104);
			colat += fprintf(out, "%u", bbr->applimited);
			colat += pad_out(colat, 111);
			colat += fprintf(out, "%u", calc1);
			colat += pad_out(colat, 119);
			colat += fprintf(out, "%u", calc2);
			colat += pad_out(colat, 127);
			colat += fprintf(out, "%u", state_send_count);
			colat += pad_out(colat, 135);
			colat += fprintf(out, "%u", state_send_bytes);
			colat += pad_out(colat, 143);
			if (bbr->use_lt_bw)
				fprintf(out, " # LTBW %s\n", state_at_to_state_name(state_at));
			else
				fprintf(out, " # DR   %s\n", state_at_to_state_name(state_at));
			out_count++;
			if (state_at == 110) {
				out_count++;
				fprintf(out, "#\n");
			}
		}
		if (bbr->bbr_state == 3) {
			state_at = 40 + (10 * bbr->bbr_substate);
		} else if (bbr->bbr_state == 1) {
			state_at = 10;
		} else if (bbr->bbr_state == 2) {
			state_at = 20;
		} else if (bbr->bbr_state == 4) {
			state_at = 30;
		} else {
			/* TSNH */
			state_at = 1000;
		}
		last_major_state = bbr->bbr_state;
		last_minor_state = bbr->bbr_substate;
		state_send_count = 0;
		max_rtt_in_state = 0;
		min_rtt_in_state = 0xffffffff;
		state_send_bytes = 0;
		del_at_state = bbr->delivered;;
		lost_at_state = bbr->lost;
		opg = bbr->pacing_gain;
		old_state = bbr->bbr_state;
		last_pg_chg = bbr->timeStamp;
		break;
	default:
		fprintf(out, " -- huh? %d\n", id);
		break;
	};
	if (change_tracking)
		change_tracking_check(l);
}

static uint32_t prev_tick=0;
static int prev_tick_set = 0;
static uint32_t next_seq=0;
static int seq_set = 0;
static uint32_t rack_last_out = 0;
static uint32_t rack_last_in = 0;
static uint32_t rack_arr_in = 0;
static uint64_t rack_sab_sum = 0;
static uint8_t rack_last_in_set = 0;
static uint8_t rack_arr_in_set = 0;
static int rack_last_out_set = 0;


static char *
translate_quality_metric(uint8_t quality)
{
	static char buffer[64];

	if (quality == RACK_QUALITY_NONE) {
		sprintf(buffer, "None Stated");
	} else if (quality == RACK_QUALITY_HIGH) {
		sprintf(buffer, "High");
	} else if (quality == RACK_QUALITY_APPLIMITED) {
		sprintf(buffer, "Low applimited");
	} else if (quality == RACK_QUALITY_PERSIST) {
		sprintf(buffer, "Low pesist");
	} else if (quality == RACK_QUALITY_PROBERTT) {
		sprintf(buffer, "Low probertt");
	} else if (quality == RACK_QUALITY_ALLACKED) {
		sprintf(buffer, "Low allacked");
	} else {
		sprintf(buffer, "Unknown");
	}
	return (buffer);
}


static int use_timestamp = 1;
static uint64_t lost_rack_count = 0;

static uint32_t min_rtt_seen, max_rtt_seen;
static int32_t prev_rtt;
static int32_t rtt_diff = 0;
static uint8_t prtt_set = 0;
static uint8_t rtt_diff_set = 0;
static uint32_t time_last_hdwr_99 = 0;
static int v6 = 0;

static uint32_t last_rtt_measure = 0;
static uint32_t gp_srtt = 0;

static int32_t gp_prev_rtt;
static int32_t gp_rtt_diff = 0;
static uint8_t gp_prtt_set = 0;
static uint8_t gp_rtt_diff_set = 0;
static uint32_t gp_lower_rtt = 0;
static uint32_t last_cwnd_to_use = 0;
static uint64_t total_log_in = 0;
static uint64_t total_log_out = 0;
static uint32_t recovery_entered = 0;
static int add_colon = 0;
static uint64_t gp_est_cnt = 0;
static uint64_t prev_gp_est = 0;

static void
dump_rack_log_entry(const struct tcp_log_buffer *l, const struct tcphdr *th)
{
	const struct tcp_log_bbr *bbr;
	uint32_t th_ack, th_seq, timeoff, calc, time_display, time_to_use;
	int id, val;
	uint32_t l_timeStamp;
	const uint8_t *optptr;
	char *mask;
	struct timeval wct;
	int32_t my_rtt_diff;
	char time_buffer[100];
	struct tcpopt to;

	bbr = &l->tlb_stackinfo.u_bbr;
	id = l->tlb_eventid;
	if (id == TCP_LOG_ACCOUNTING) {
		dump_accounting(l);
		return;
	}
	l_timeStamp = bbr->timeStamp;
	if (id == TCP_LOG_SOCKET_OPT) sock_opt_cnt++;
	if ((id == TCP_LOG_USERSEND) ||
	    (id == TCP_LOG_FLOWEND) ||
	    (id == TCP_LOG_CONNEND) ||
	    (id == TCP_LOG_PRU) ||
	    (id == TCP_LOG_SENDFILE) ||
	    (id == TCP_LOG_SOCKET_OPT)){
		l_timeStamp = (uint32_t) ((l->tlb_tv.tv_sec * HPTS_USEC_IN_SEC) + l->tlb_tv.tv_usec);
	}
	if (tlb_sn_set > 0) {
		if ((tlb_sn+1) != l->tlb_sn) {
			if (tlb_sn > l->tlb_sn) {
				duplicates++;
				fprintf(out, "Last sn:%u new sn is now %u -- flowed backwards?\n",
					tlb_sn, l->tlb_sn);
				goto backward;
			}
			fprintf(out, "***Missing sn:%d -> l->tlb_sn:%d ****\n", tlb_sn, l->tlb_sn);
			total_missed_records += (l->tlb_sn - tlb_sn);
		}
	}
backward:
	tlb_sn = l->tlb_sn;
	tlb_sn_set = 1;
	if (use_timestamp)
		time_to_use = l_timeStamp;
	else
		time_to_use = l->tlb_ticks;
	if (first_time_set == 0) {
		time_entered = time_to_use;
		first_time = time_to_use;
		first_time_set = 1;
	}
	if (prev_tick == 0) {
		prev_tick_set = time_to_use;
		prev_tick = 1;
	}
	/* Deterime state and log time */
	if (IN_RECOVERY(l->tlb_flags)) {
		/* recovery */
		if (gp_state != STATE_REC) {
			add_time_to_state(time_to_use, STATE_REC);
		} else if (TSTMP_GT(time_to_use, time_entered)) {
			time_in_state[gp_state] += (time_to_use - time_entered);
			time_entered = time_to_use;
		}
	} else if (l->tlb_snd_ssthresh > l->tlb_snd_cwnd) {
		/* Slow start */
		if (gp_state != STATE_SS) {
			add_time_to_state(time_to_use, STATE_SS);
		} else if (TSTMP_GT(time_to_use, time_entered)) {
			time_in_state[gp_state] += (time_to_use - time_entered);
			time_entered = time_to_use;
		}
	} else {
		/* Congestion avoidance */
		if (gp_state != STATE_CA) {
			add_time_to_state(time_to_use, STATE_CA);
		} else if (TSTMP_GT(time_to_use, time_entered)) {
			time_in_state[gp_state] += (time_to_use - time_entered);
			time_entered = time_to_use;
		}
	}
	if (time_is_relative && first_time_set) {
		time_display = time_to_use - first_time;
	} else {
		time_display = time_to_use;
	}
	if (TSTMP_GT(time_to_use, prev_tick))
		timeoff = time_to_use - prev_tick;
	else
		timeoff = 0;
	prev_tick = time_to_use;
	if (rack_last_out_set == 0) {
		rack_last_out = prev_tick;
		rack_last_out_set = 1;
	}
	if ((lh != NULL) && showExtraInfo) {
		fprintf(stdout, "id:%s: tag:%s \n",
			lh->tlh_id,
			lh->tlh_tag);
		showExtraInfo = 0;
	}
	if (lh != NULL) {
		struct tm *tmval;

		if (tag_dumped == 0) {
			tag_dumped = 1;
			strcpy(log_tag, lh->tlh_tag);
		}
		wct.tv_sec = lh->tlh_offset.tv_sec + l->tlb_tv.tv_sec;
		wct.tv_usec = lh->tlh_offset.tv_usec + l->tlb_tv.tv_usec;
		while (wct.tv_usec > 1000000) {
			wct.tv_usec -= 1000000;
			wct.tv_sec++;
		}
		last_time.tv_sec = wct.tv_sec;
		last_time.tv_usec = wct.tv_usec;
		tmval = gmtime(&wct.tv_sec);
		if ((tmval == NULL) || (display_wallclock_time == 0))
			goto skip_time;
		if (display_wallclock_time)
			sprintf(time_buffer, "%2.2u:%2.2u:%2.2u.%6.6u UTC",
				tmval->tm_hour,
				tmval->tm_min,
				tmval->tm_sec,
				(int)wct.tv_usec);
	} else {
	skip_time:
		sprintf(time_buffer, "%u", time_display);
	}
	if ((lh != NULL) && early_filled == 0) {
		uint32_t ticks_passed, sec, usec;

		early_filled = 1;
		earliest_time.tv_sec = wct.tv_sec;
		earliest_time.tv_usec = wct.tv_usec;
		connection_begin_time.tv_sec = earliest_time.tv_sec;
		connection_begin_time.tv_usec = earliest_time.tv_usec;
		/* Now how many ticks since we started have passed? */
		ticks_passed = l->tlb_ticks - l->tlb_starttime;
		/* Back up our earliest time by that many ticks */
		sec = ticks_passed / 1000;
		usec = ticks_passed % 1000;
		usec *= 1000;
		if (usec > earliest_time.tv_usec) {
			connection_begin_time.tv_sec--;
			connection_begin_time.tv_usec += 1000000;
		}
		connection_begin_time.tv_usec -= usec;
		connection_begin_time.tv_sec -= sec;
	}
	if (show_record) {
		if (use_monolithic_time)
			sprintf(time_buffer, "%lu.%6.6lu",
				l->tlb_tv.tv_sec,
				l->tlb_tv.tv_usec);
		fprintf(out, "|%u| %s %u rack [%u] %s ",
			l->tlb_sn, time_buffer, number_flow, timeoff, evt_name(id));

	} else {
		if (display_wallclock_time)
			fprintf(out, "%s|%u %u rack [%u] %s ",
				time_buffer,
				time_display, number_flow, timeoff, evt_name(id));
		else if (use_monolithic_time) {
			sprintf(time_buffer, "%lu.%6.6lu",
				l->tlb_tv.tv_sec,
				l->tlb_tv.tv_usec);
			fprintf(out, "%s|%u %u rack [%u] %s ",
				time_buffer,
				time_display, number_flow, timeoff, evt_name(id));
		} else {
			if (add_colon)
				fprintf(out, "%u: %u rack [%u] %s ",
					time_display, number_flow, timeoff, evt_name(id));
			else 
				fprintf(out, "%u %u rack [%u] %s ",
					time_display, number_flow, timeoff, evt_name(id));

		}
	}
	switch (id) {
	case BBR_LOG_CWND:
		if ((bbr->flex8 == 0) ||
		    (bbr->flex8 == 1)) {
			fprintf(out, " cwnd update orig_cw:%u ssthresh:%u snd_max:%u th_ack:%u (%u) ccv->flags:0x%x bytes_this_ack:%u nsegs:%u abc_val:%u rfc6675:%u\n",
				l->tlb_snd_cwnd,
				l->tlb_snd_ssthresh,
				l->tlb_snd_max,
				bbr->flex1,
				(l->tlb_snd_max - bbr->flex1),
				bbr->flex2,
				bbr->flex3,
				bbr->flex4,
				bbr->flex5,
				bbr->flex7);
			print_out_space(out);
			fprintf(out, " ---> new_cw:%u\n", bbr->flex6);
		} else if (bbr->flex8 == 2) {
			fprintf(out, " post_recovery orig_cw:%u ssthresh:%u snd_max:%u th_ack:%u (%u) ccv->flags:0x%x bytes_this_ack:%u nsegs:%u abc_val:%u rfc6675:%u\n",
				bbr->flex6,
				l->tlb_snd_ssthresh,
				l->tlb_snd_max,
				bbr->flex1,
				(l->tlb_snd_max - bbr->flex1),
				bbr->flex2,
				bbr->flex3,
				bbr->flex4,
				bbr->flex5,
				bbr->flex7);
			print_out_space(out);
			fprintf(out, " ---> new_cw:%u\n", l->tlb_snd_cwnd);

		} else if (bbr->flex8 == 3) {
			fprintf(out, " Cwnd Beta changes beta:%u beta_ecn:%u flags:0x%x old_beta:%u old_beta_ecn:%u old_flags:0x%x GP_R|FIXED|PACING_SET:0x%x\n",
				bbr->flex1, bbr->flex2, bbr->flex3,
				bbr->flex4, bbr->flex5, bbr->flex6, bbr->flex7);
		} else if (bbr->flex8 == 4) {
			fprintf(out, " Cwnd Restore Beta to beta:%u beta_ecn:%u flags:0x%x saved_beta:%u saved_beta_ecn:%u saved_flags:0x%x GP_R|FIXED|PACING_SET:0x%x\n",
				bbr->flex1, bbr->flex2, bbr->flex3,
				bbr->flex4, bbr->flex5, bbr->flex6, bbr->flex7);
		} else if (bbr->flex8 == 5) {
			uint64_t stored_gp;

			fprintf(out, " Cwnd Clamped due to excess rxt ncwnd:%u nssthresh:%u cwnd:%u ssthresh:%u max_seg:%u fillcw:%u\n",
				bbr->flex1, bbr->flex2,
				l->tlb_snd_cwnd, l->tlb_snd_ssthresh,
				bbr->pkt_epoch, bbr->bbr_state);
			print_out_space(out);
			fprintf(out, " rnds:%u min_rnds:%u rack_rtt:%u rxts:%lu snds:%lu thresh:%lu del_bw:%s (%lu) avg_rxt_cnt:%u\n",
				bbr->flex3, bbr->flex4,
				bbr->flex5,
				bbr->cur_del_rate, bbr->delRate,
				bbr->rttProp,
				display_bw(bbr->bw_inuse, 0), bbr->bw_inuse, bbr->flex7);
			print_out_space(out);
			stored_gp = bbr->lt_epoch;
			stored_gp <<= 32;
			stored_gp |= bbr->pkts_out;
			fprintf(out, "Clamps applied:%u Max:%u gp_bw:%s (%lu) min_to:%u\n",
				bbr->delivered, bbr->applimited, 
				display_bw(stored_gp, 0), stored_gp, bbr->epoch);
		} else if (bbr->flex8 == 6) {
			uint64_t bw;

			bw = bbr->lt_epoch;
			bw <<= 32;
			bw |= bbr->pkts_out;
			if(bbr->bbr_state == 0) {
				fprintf(out, "ProbeUp Done Clamp removed rnds:%u unclamp_rnd_thresh:%u rxt_per:%u rxt_thresh:%u lt_bw:%s (%lu) ",
					bbr->flex3, bbr->flex4, bbr->flex5, bbr->flex1,
					display_bw(bbr->bw_inuse, 0), bbr->bw_inuse);
				fprintf(out, " gp_bw:%s (%lu) rxt_per:%u cwnd:%u\n",
					display_bw(bw, 0), bw, bbr->flex5, l->tlb_snd_cwnd);
			} else {
				fprintf(out, "ProbeUp Done - clamp remains - rxt_per:%u rxt_thresh:%u lt_bw:%s (%lu) ",
					bbr->flex5, bbr->flex1,
					display_bw(bbr->bw_inuse, 0), bbr->bw_inuse);
				fprintf(out, " gp_bw:%s (%lu) rxt_per:%u snds:%lu rxt:%lu cwnd:%u\n",
					display_bw(bw, 0), bw, bbr->flex5,
					bbr->delRate, bbr->cur_del_rate,
					l->tlb_snd_cwnd);
			}
		} else if (bbr->flex8 == 20) {
			uint64_t per;

			if (bbr->delRate) {
				per  = (bbr->cur_del_rate * 1000)/bbr->delRate;
			} else {
				per = 0;
			}
			fprintf(out, "Clamp check rnds_req:%u rnds:%u thresh:%lu snds:%lu rxt:%lu rxt_amm:%lu\n",
				bbr->flex4, bbr->flex3,	bbr->rttProp,
				bbr->delRate, bbr->cur_del_rate, per);
		} else if (bbr->flex8 == 21) {
			uint64_t rate;

			if (bbr->delRate)
				rate = (bbr->cur_del_rate * 1000) / bbr->delRate;
			else
				rate = 0;
			fprintf(out, "Clamp update cwnd new_cwnd:%u old_saved:%u lt_bw:%s(%lu) rtt:%u cur_rnd:%u rxt:%lu snds:%lu rper:%lu\n",
				bbr->flex1,
				bbr->flex2,
				display_bw(bbr->bw_inuse, 0), bbr->bw_inuse,
				bbr->flex5, bbr->applimited, bbr->cur_del_rate,
				bbr->delRate, rate);
		} else if (bbr->flex8 == 22) {
			uint64_t bw;

			bw = bbr->lt_epoch;
			bw <<= 32;
			bw |= bbr->pkts_out;
			fprintf(out, "UN-Clamp fails rnds:%u unclamp_rnd_thresh:%u rxt_per:%u rxt_thresh:%u lt_bw:%s (%lu) ",
				bbr->flex3, bbr->flex4, bbr->flex5, bbr->flex1,
				display_bw(bbr->bw_inuse, 0), bbr->bw_inuse);
			fprintf(out, " gp_bw:%s (%lu) rxt_per:%u cur_rnd:%u cwnd:%u\n",
				display_bw(bw, 0), bw, bbr->flex5, bbr->applimited, l->tlb_snd_cwnd);
		} else if (bbr->flex8 == 23) {
			uint64_t bw;

			bw = bbr->lt_epoch;
			bw <<= 32;
			bw |= bbr->pkts_out;
			fprintf(out, "Probe-up to unclamp begins rnds:%u unclamp_rnd_thresh:%u rxt_per:%u rxt_thresh:%u lt_bw:%s (%lu) ",
				bbr->flex3, bbr->flex4, bbr->flex5, bbr->flex1,
				display_bw(bbr->bw_inuse, 0), bbr->bw_inuse);
			fprintf(out, " gp_bw:%s (%lu) rxt_per:%u cur_rnd:%u cwnd:%u\n",
				display_bw(bw, 0), bw, bbr->flex5, bbr->applimited, l->tlb_snd_cwnd);

		} else if (bbr->flex8 == 24) {
			uint64_t bw;

			bw = bbr->lt_epoch;
			bw <<= 32;
			bw |= bbr->pkts_out;
			fprintf(out, "Cannot Probe-up rxt high rnds:%u unclamp_rnd_thresh:%u rxt_per:%u rxt_thresh:%u lt_bw:%s (%lu) ",
				bbr->flex3, bbr->flex4, bbr->flex5, bbr->flex1,
				display_bw(bbr->bw_inuse, 0), bbr->bw_inuse);
			fprintf(out, " gp_bw:%s (%lu) rxt_per:%u cur_rnd:%u cwnd:%u\n",
				display_bw(bw, 0), bw, bbr->flex5, bbr->applimited, l->tlb_snd_cwnd);
		} else if (bbr->flex8 == 40) {
			fprintf(out, "Slowstart ended Rnd:%u last rise rnd:%u thresh:%u\n",
				bbr->flex1, bbr->flex2, bbr->flex3);
		} else if (bbr->flex8 == 41) {
			fprintf(out, "Assess Rnd:%u current gp:%lu last_rise_est:%lu ",
				bbr->flex1,
				bbr->delRate,
				bbr->cur_del_rate);
			if (bbr->delRate < bbr->cur_del_rate) {
				fprintf(out, " last rise round %u\n", bbr->flex2);
			} else {
				double top, bot, per;

				top = bbr->delRate * 100.0;
				bot = bbr->cur_del_rate  * 1.0;
				per = top / bot;
				fprintf(out, " rise %2.4f %% last rise round %u\n",
					per, bbr->flex2);
			}
		} else if (bbr->flex8 == 42) {
			fprintf(out, "It Incremented Rnd:%u inc by:%u thresh:%u\n",
				bbr->flex1, bbr->flex2, 
				bbr->flex3);

		} else if (bbr->flex8 == 44) {
			fprintf(out, "Multiplier %u gp:%lu lt_bw:%lu restricted rate:%lu fill-cw:%lu (len:%u)\n",
				bbr->flex1,
				bbr->cur_del_rate,
				bbr->delRate,
				bbr->bw_inuse,
				bbr->rttProp, bbr->flex2);
		} else if (bbr->flex8 == 55) {
			fprintf(out, "B/W calc len:%u segs:%u slot%u gain:%u rw:%lu get_bw:%lu lentim:%lu\n",
				bbr->flex1, bbr->flex2,
				bbr->flex3, bbr->flex4,
				bbr->cur_del_rate,
				bbr->rttProp, bbr->delRate);
				
		} else {
			fprintf(out, " Unknown Cwnd log flex8:%u\n", bbr->flex8);
		}
		break;
	case BBR_LOG_HDWR_PACE:
	{
		uint64_t hw_bw;
		uint64_t ptr;
		char *bwd, *hw_bwd, *req_bwd;
		const char *str;

		if (bbr->flex7 == 99) {
			fprintf(out,
				"Hardware Queue Measurement rate:%u queue:%u crte_r:%s(%lu) using:%u enobufs:%u time_bet:%u (sah:%u)\n",
				bbr->flex1, bbr->flex2,
				display_bw(bbr->delRate, 0),
				bbr->delRate,
				bbr->flex4,
				bbr->flex5,
				bbr->flex6,
				(time_last_hdwr_99 > 0) ? bbr->timeStamp - time_last_hdwr_99 : 0);
			time_last_hdwr_99 = bbr->timeStamp;
			if (time_last_hdwr_99 == 0)
				time_last_hdwr_99 = 1;
			break;
		}
		bwd = display_bw(bbr->delRate, 1);
		req_bwd = display_bw(bbr->bw_inuse, 1);
		hw_bw = bbr->flex1;
		hw_bw <<= 32;
		hw_bw |= bbr->flex2;
		hw_bwd = display_bw(hw_bw, 1);

		ptr = bbr->flex3;
		ptr <<= 32;
		ptr |= bbr->flex4;
		if (bbr->flex7 == 0) {
			str = "Initial hardware rate acquired";
		} else if (bbr->flex7 == 1) {
			str = "Hardware cannot meet request -- lost hw pacing";
		} else if (bbr->flex7 == 2) {
			str = "Hardware rate updated";
		} else if (bbr->flex7 == 3) {
			str = "Capped at hardware rate";
		} else if (bbr->flex7 == 4) {
			str = "No rate change, update pace size";
		} else if (bbr->flex7 == 5) {
			str = "Rate falls below hardware minimum -- drop rate";
		} else if (bbr->flex7 == 6) {
			str = "Lost inp_snd_tag must re-attempt";
		} else {
			str = "Unknown log_hdwr_pace type";
		}
		fprintf(out,
			"Line:%d %s(%d) ifp:0x%lx err:%d (DR:%s req_BW:%s hw_bw:%s) max_segs:%u\n",
			bbr->flex5,
			str, bbr->flex7,
			ptr, bbr->flex6,
			bwd, req_bwd, hw_bwd,
			bbr->applimited);
		if (bwd)
			free(bwd);
		if (req_bwd)
			free(req_bwd);
		if (hw_bwd)
			free(hw_bwd);
		if (extra_print) {
			char *cur_hw_rate, *prev_rate_in_table, *last_saved_rate;
			const char *chwr, *prit, *lsr;

			if (bbr->cur_del_rate) {
				cur_hw_rate = display_bw(bbr->cur_del_rate, 1);
				chwr = cur_hw_rate;
			} else {
				cur_hw_rate = NULL;
				chwr = "None specified";
			}
			if (bbr->delRate) {
				prev_rate_in_table = display_bw(bbr->delRate, 1);
				prit = prev_rate_in_table;
			} else {
				prev_rate_in_table = NULL;
				prit = "None specified";
			}
			if (bbr->rttProp) {
				last_saved_rate = display_bw(bbr->rttProp, 1);
				lsr = last_saved_rate;
			} else {
				last_saved_rate = NULL;
				lsr = "None specified";
			}
			print_out_space(out);
			fprintf(out, "hw_rate:%s(%lu) prev_rate_in_tbl:%s(%lu) previous_req_rate:%s(%lu)\n",
				chwr, bbr->cur_del_rate,
				prit, bbr->delRate,
				lsr, bbr->rttProp);
			if (cur_hw_rate)
				free(cur_hw_rate);
			if (prev_rate_in_table)
				free(prev_rate_in_table);
			if (last_saved_rate)
				free(last_saved_rate);
		}
	}
	break;
	case BBR_LOG_HPTSI_CALC:
	{
		uint64_t bw_est, bw_raise;

		bw_est = bbr->bw_inuse;
		bw_raise = bbr->delRate;
		if (bbr->flex8 == 1) {
			fprintf(out, "Setting GP INCR CA mult=%u, SS mult=%u REC mult:%lu line:%d minrtt:%u\n",
				bbr->flex1,
				bbr->flex2, bbr->bw_inuse, bbr->pkt_epoch, bbr->pkts_out);
		} else if (bbr->flex8 == 2) {
			char *rbw;
			const char *ccmode;
			double multiplier;

			if (IN_RECOVERY(l->tlb_flags)) {
				ccmode = "REC";
				multiplier = (bbr->applimited  * 1.0);
			} else if ((bbr->flex7 & 1) == 0) {
				ccmode = "CA";
				multiplier = (bbr->flex6 * 1.0);
			} else {
				ccmode = "SS";
				multiplier = (bbr->flex5 * 1.0);
			}
			rbw = display_bw(bw_raise, 1);
			fprintf(out, "mode:%d len:%u slot:%u min_seg:%u max_seg:%u gain:%u min_rtt:%u smRSC:0x%x mode:%s rate_wanted:%s\n",
				bbr->flex8,
				bbr->flex2,
				bbr->flex1, bbr->flex3, bbr->flex4, bbr->pacing_gain, bbr->pkts_out, bbr->cwnd_gain, ccmode, display_bw(bw_est, 0)
				);
			print_out_space(out);
			fprintf(out, " rw:%s (%lu) actual_bw:%s (%lu) multiplier:%2.3f%% avail:%u bbrstate:0x%x\n",
				display_bw(bw_est, 0),
				bw_est,
				rbw,
				bw_raise, multiplier,
				l->tlb_txbuf.tls_sb_acc, bbr->bbr_state);
			if (rbw != NULL)
				free(rbw);
		} else  if (bbr->flex8 == 3) {
			uint64_t tim, bytes_ps;
			uint32_t time_delta;
			int32_t new_rtt_diff;
			char *gbw, *bwest;
			const char *override;
			double norm_grad;
			const char *s1, *s2;
			static char dump_buf[200];
			/* Calculate the GP value */
			s1 = s2 = " ";
			if ((uint32_t)bbr->delRate > bbr->flex1) {
				s2 = "*";
				time_delta = (uint32_t)bbr->delRate - bbr->flex1;
				tim = bbr->delRate;
			} else {
				s1 = "*";
				time_delta = bbr->flex1 - (uint32_t)bbr->delRate;
				tim = bbr->flex1;
			}
			gp_est_cnt++;
			bytes_ps = (uint64_t)bbr->flex2;
			bytes_ps *= 1000000;
			bytes_ps /= tim;
			if (gp_est_cnt <= 4) {
				sprintf(dump_buf, "EARLY");
			} else {
				double delta_per, top, bot;
				if (prev_gp_est < bbr->rttProp) {
					top = (bbr->rttProp * 1.0);
					bot = (prev_gp_est * 1.0);
					delta_per = top / bot;
					sprintf(dump_buf,"+%3.5f", delta_per);
				} else {
					top = (prev_gp_est * 1.0);
					bot = (bbr->rttProp * 1.0);
					delta_per = top / bot;
					sprintf(dump_buf, "-%3.5f", delta_per);
				}
				
			}
			prev_gp_est = bbr->rttProp;
			gbw = display_bw(bbr->rttProp, 1);
			bwest = display_bw(bytes_ps, 1);
			fprintf(out, "GP est Quality: %s TIMELY gput:%s(%lu) new GP value %s(%lu %s) [len:%u tim:%u%s stim:%lu%s] minrtt:%u gain:%u AGSP:0x%x  RSC:0x%x\n",
				translate_quality_metric(bbr->bbr_substate),
				bwest,
				bytes_ps,
				gbw,
				bbr->rttProp,
				dump_buf,
				bbr->flex2,
				bbr->flex1, s1,
				bbr->delRate, s2,
				bbr->pkts_out, bbr->pacing_gain, bbr->use_lt_bw, bbr->cwnd_gain);
			/* Calculate the gp based INC/Dec based on Timely */
			if (gp_prtt_set == 0) {
				gp_prtt_set = 1;
				gp_prev_rtt = gp_srtt;
				new_rtt_diff = 0;
				norm_grad = 0.0;
			} else {
				new_rtt_diff = (int32_t)gp_srtt - (int32_t)gp_prev_rtt;
				gp_prev_rtt = gp_srtt;
				if (rtt_diff_set == 0) {
					gp_rtt_diff = new_rtt_diff;
					gp_rtt_diff_set = 1;
				} else {
					/*
					 * lets take 1/8 of the new diff
					 * and add it to 7/8th the old
					 * to get a EWMA
					 */
					gp_rtt_diff -= (gp_rtt_diff/8);
					gp_rtt_diff += (new_rtt_diff/8);
				}
				norm_grad = (double)gp_rtt_diff / (double)min_rtt_seen;
				/* Update the GP  measurement based srtt */
				gp_srtt -= (gp_srtt / 8);
				gp_srtt += (bbr->flex1 / 8);
			}
			/* Restart GP srtt measurements */
			if (gp_srtt > (4 * min_rtt_seen)) {
				override = "RED";
			} else if (gp_srtt < (min_rtt_seen + (min_rtt_seen/2))) {
				override = "INC";
			} else {
				override = "USE GRAD";
			}
			gp_srtt = last_rtt_measure;
			print_out_space(out);
			fprintf(out, "Norm_grad:%f-(%s) gp_rtt_diff:%d OVER:%s\n",
				norm_grad,
				((norm_grad <= 0.0) ? "INC" : "DEC"),
				gp_rtt_diff,
				override
				);

			if (extra_print) {
				uint32_t amo, sub;

				print_out_space(out);
				sub = (l->tlb_snd_max - l->tlb_snd_una);
				if (l->tlb_txbuf.tls_sb_acc > sub)
					amo = l->tlb_txbuf.tls_sb_acc - sub;
				else
					amo = 0;
				fprintf(out, "lrc:%lu out:%u avail:%u amo:%u snd_wnd:%u time-delta:%u\n",

					lost_rack_count,
					(l->tlb_snd_max - l->tlb_snd_una),
					l->tlb_txbuf.tls_sb_acc,
					amo,
					l->tlb_snd_wnd > l->tlb_snd_cwnd ? l->tlb_snd_cwnd : l->tlb_snd_wnd, time_delta);
			}
			if (gbw)
				free(gbw);
			if (bwest)
				free(bwest);
		} else  if (bbr->flex8 == 4) {
			fprintf(out, "GP Stopped by limited old-gpack:%u snd_max:%u (marked lim) new-gpack:%lu appl:%d\n",
				bbr->flex1, l->tlb_snd_max,
				bbr->bw_inuse,
				bbr->flex2);
			if (extra_print) {
				print_out_space(out);
				fprintf(out, "t_flags:0x%x t_flags2:0x%x\n", l->tlb_flags, l->tlb_flags2);
			}
		} else  if (bbr->flex8 == 5) {
			uint32_t oldseq, newseq;

			oldseq = bbr->bw_inuse;
			newseq = bbr->delRate;
			if (use_relative_seq) {
				oldseq -= l->tlb_iss;
				newseq -= l->tlb_iss;
			}
			fprintf(out, "Change GP range oldts:%u newts:%u oldseq:%u newseq:%u line:%u AGSP:0x%x t_flags:0x%x t_flags2:0x%x\n",
				bbr->flex2, bbr->flex1,
				oldseq, newseq,
				bbr->pkt_epoch, bbr->use_lt_bw, l->tlb_flags, l->tlb_flags2);
		} else  if (bbr->flex8 == 6) {
			fprintf(out, "Aborted measurment app limited case reduced to %u bytes AGSP:0x%x t_flags:0x%x t_flags2:0x%x\n",
				bbr->flex2 - bbr->flex1, bbr->use_lt_bw, l->tlb_flags, l->tlb_flags2);
		} else  if (bbr->flex8 == 7) {
			fprintf(out, "Old rack burst mitigation len:%u slot:%u trperms:%lu reduce:%lu minrtt:%u bbrstate:0x%x\n",
				bbr->flex2, bbr->flex1, bbr->bw_inuse, bbr->delRate, bbr->pkts_out, bbr->bbr_state);
		} else if (bbr->flex8 == 8) {
			fprintf(out, "Setting Fixed Pacing CA mult=%u, SS mult=%u REC mult:%lu line:%d minrtt:%u\n",
				bbr->flex1,
				bbr->flex2, bbr->bw_inuse, bbr->pkt_epoch, bbr->pkts_out);
		} else  if (bbr->flex8 == 9) {
			uint32_t to_ack, frm_seq, snd_max, snd_una;

			to_ack = bbr->flex1;
			frm_seq = bbr->flex2;
			snd_una = l->tlb_snd_una;
			snd_max = l->tlb_snd_max;
			if (use_relative_seq) {
				to_ack -= l->tlb_iss;
				frm_seq -= l->tlb_iss;
				snd_una -= l->tlb_iss;
				snd_max -= l->tlb_iss;
			}
			fprintf(out, "GP Measure to_ack:%u frm_seq:%u (len:%u) snd_una:%u snd_max:%u rsm:0x%lx alc:%lu LINE:%d AGSP:0x%x\n",
				to_ack, frm_seq, (to_ack - frm_seq),
				snd_una,
				snd_max,
				bbr->bw_inuse,
				((bbr->rttProp >> 32) & 0x00000000ffffffff),
				bbr->pkt_epoch,
				bbr->use_lt_bw);
			if (extra_print) {
				uint32_t out_ts;

				print_out_space(out);
				out_ts = (bbr->rttProp & 0x00000000ffffffff);
				fprintf(out, "start_ts:%lu minrtt:%u out_ts:%u path:%u\n",
					bbr->delRate, bbr->pkts_out, out_ts, bbr->bbr_substate);
			}
		} else  if (bbr->flex8 == 10) {
			fprintf(out, "Aborted measurment too short req:%u actual:%u AGSP:0x%x line:%d t_flags:0x%x t_flags2:0x%x\n",
				bbr->flex1, bbr->flex2, bbr->use_lt_bw,
				bbr->pkt_epoch, l->tlb_flags, l->tlb_flags2);
		} else  if (bbr->flex8 == 11) {
			char *c_bw, *m_bw;
			c_bw = display_bw(bbr->bw_inuse, 1);
			m_bw = display_bw(bbr->delRate, 1);
			fprintf(out, "Calculated b/w:%s(%lu) exceeds max possible b/w:%s(%lu) AGSP:0x%x\n",
				c_bw,
				bbr->bw_inuse,
				m_bw,
				bbr->delRate,
				bbr->use_lt_bw);
			free(c_bw);
			free(m_bw);
		} else if (bbr->flex8 == 12) {
			fprintf(out, "fill-cw override Slot:%d len:%u override to ns:%lu bw:%s(%lu)\n",
				bbr->flex1, bbr->flex2,
				bbr->rttProp,
				display_bw(bbr->bw_inuse, 0),
				bbr->bw_inuse);
		} else if (bbr->flex8 == 14) {
			fprintf(out, "fill-cw in non-paced mode slot:%u bw:%s(%lu) ALEAGMIR:0x%x\n",
				bbr->flex1,
				display_bw(bbr->bw_inuse, 0),
				bbr->bw_inuse,
				bbr->use_lt_bw);
		} else if (bbr->flex8 == 15) {
			fprintf(out, "Setting pacing max seg set was %lu now at %u line:%u minrtt:%u\n",
				bbr->bw_inuse, bbr->flex4, bbr->pkt_epoch, bbr->pkts_out);
		} else if (bbr->flex8 == 17) {
			fprintf(out, "Logging started tim:%u exceeds threshold gp_srtt:%u len:%lu\n",
				bbr->flex2,
				bbr->flex1,
				bbr->bw_inuse);
		} else if (bbr->flex8 == 18) {
			fprintf(out, "Canceling GP estimate len:%u not available gp_srtt:%u state:%u line:%d\n",
				bbr->flex2,
				bbr->flex1, l->tlb_state, bbr->pkt_epoch);
		} else if (bbr->flex8 == 19) {
			fprintf(out, "Logging started tim:%u smaller than our threshold  gp_srtt:%u len:%lu\n",
				bbr->flex2,
				bbr->flex1,
				bbr->bw_inuse);
		} else if (bbr->flex8 == 20) {
			char *bw_e, *gp_bw;
			bw_e = display_bw(bbr->bw_inuse, 1);
			gp_bw = display_bw(bbr->delRate, 1);
			fprintf(out, "GP summary est:%s(%lu) gp_bw:%s(%lu)**unscaled  lt_bw:%s(%lu) line:%u\n",
				bw_e, bbr->bw_inuse,
				gp_bw, bbr->delRate,
				display_bw(bbr->rttProp, 0), bbr->rttProp, bbr->pkt_epoch);
			if (bw_e)
				free(bw_e);
			if (gp_bw)
				free(gp_bw);
		} else if (bbr->flex8 == 22) {
			fprintf(out, "Addpart:%u Subpart:%u %s add (%d) flags:0x%x bw:%lu\n",
				bbr->flex1,
				bbr->flex2,
				((bbr->pkts_out > 0)?  "Performed" : "Skipped"),
				bbr->pkt_epoch,
				bbr->use_lt_bw,
				bbr->delRate
				);
		} else if (bbr->flex8 == 26) {
			/*
			 * Flags are set in use_lt_bw and indicate:
			 * A - Ack can send out data.
			 * L - Late flag for pacing
			 * E - Early flag for pacing
			 * A - App limited needs set for GP measurements
			 * G - Goodput filled
			 * M - Measurement interval saw probe rtt
			 * I - In probe RTT
			 * R - Goodput measurement is ready
			 */
			fprintf(out, "ALEAGMIR:0x%x delayed:%u early:%u\n",
				bbr->use_lt_bw,
				bbr->epoch, bbr->lt_epoch);
				
		} else if (bbr->flex8 == 27) {
			fprintf(out, "Timer setup slot originally:%u we use %u ALEAGMIR:0x%x delayed:%u earlly:%u\n",
				bbr->flex2, bbr->flex1,
				bbr->use_lt_bw,
				bbr->epoch, bbr->lt_epoch);
		} else if (bbr->flex8 == 30) {
			const char *dgp_on, *less_agg, *fillcw, *dis;
			int discount;
			
			if (bbr->bbr_state & 0x10) {
				dgp_on = "DGP active";
			} else {
				dgp_on = "DGP inactive";
			}
			if (bbr->bbr_state & 0x4) {
				fillcw = "fillCw on";
				if (bbr->bbr_state & 0x8) {
					less_agg = "Less Aggressive fillcw";
				} else {
					less_agg = "More Aggressive fillcw";
				}
			} else {
				fillcw = "fillCw off";
				less_agg = " - is off - ";
			}
			discount = bbr->bbr_state & 0x3;
			if (bbr->bbr_state & 0x3) {
				dis = "Discount active";
			} else {
				dis = "Discount in-active";
			}

			fprintf(out, "Buffer Level Now %u %s, %s, %s, %s discount:%u (cfg:%u) cw:%u\n",
				bbr->flex1,
				dgp_on, fillcw, less_agg, dis, discount, bbr->flex2, l->tlb_snd_cwnd);
		} else if (bbr->flex8 == 69) {
			const char *strnm;
			
			if (bbr->flex7 == 1) 
				strnm = "Setup";
			else if (bbr->flex7 == 2)
				strnm = "Change";
			else if (bbr->flex7 == 3)
				strnm = "Measure";
			else if (bbr->flex7 == 4)  {
				/* This happens when not all the RSM is consumed */
				strnm = "Acked UPD full";
			} else if (bbr->flex7 == 5) {
				/* This happens when the entire RSM is consumed */
				strnm = "Acked UPD part";
			}else if (bbr->flex7 == 6)
				strnm = "New send UPD send end ts";
			else if (bbr->flex7 == 7)
				strnm = "Rxt send UPD send end ts";
			else
				strnm = "Unknown";
			if ((bbr->flex7 == 4) || (bbr->flex7 == 5)) {
				uint32_t gput_seq, gput_ack, rsm_start, rsm_end;

				if (use_relative_seq) {
					gput_seq = bbr->flex2 - l->tlb_iss;
					gput_ack = bbr->flex6 - l->tlb_iss;
					rsm_start = bbr->applimited - l->tlb_iss;
					rsm_end = bbr->delivered - l->tlb_iss;
				} else {
					gput_seq = bbr->flex2;
					gput_ack = bbr->flex6;
					rsm_start = bbr->applimited;
					rsm_end = bbr->delivered;
				}
				fprintf(out, "Measurement %s gput_seq:%u gput_ack:%u rsm_start:%u rsm_end:%u [len:%u]\n",
					strnm,
					gput_seq,
					gput_ack,
					rsm_start,
					rsm_end,
					(rsm_end - rsm_start));
			} else if ((bbr->flex7 == 6) || (bbr->flex7 == 7)) {
				uint32_t rsm_s, rsm_e;

				if (use_relative_seq) {
					rsm_s = bbr->flex1 - l->tlb_iss;
					rsm_e = bbr->flex3 - l->tlb_iss;
				} else {
					rsm_s = bbr->flex1;
					rsm_e = bbr->flex3;
				}
				fprintf(out, "Measurement %s rsm_s:%u rsm_e:%u end_send_ts:%lu\n",
					strnm,
					rsm_s, rsm_e,
					bbr->rttProp);
			} else {
				uint32_t snd_max, snd_una, seq_start, seq_end;
				
				if (use_relative_seq) {
					snd_max = l->tlb_snd_max - l->tlb_iss;
					snd_una = l->tlb_snd_una - l->tlb_iss;
					seq_start = bbr->flex2 - l->tlb_iss;
					seq_end = bbr->flex1 - l->tlb_iss;
				} else {
					snd_max = l->tlb_snd_max;
					snd_una = l->tlb_snd_una;
					seq_start = bbr->flex2;
					seq_end = bbr->flex1;
				}
				fprintf(out,
					"Measurement %s seq_start:%u seq_end:%u [len:%u] snd_una:%u snd_max:%u line:%d\n",
					strnm, seq_start, seq_end,
					(seq_end - seq_start),
					snd_una,
					snd_max, bbr->pkts_out);
			}
			print_out_space(out);
			fprintf(out, "                  ack_ts_start:%u ack_ts_end:%u aplnset:%u\n",
				bbr->flex4, bbr->flex3, bbr->cwnd_gain);
			print_out_space(out);			
			fprintf(out, "                  snd_ts_start:%u snd_ts_end:%u apl_cnt:%u seqs:%u seqe:%u flags:0x%x\n",
				(uint32_t)bbr->delRate, (uint32_t)bbr->rttProp, bbr->pkt_epoch,
				bbr->applimited, bbr->delivered, bbr->epoch);
		} else if (bbr->flex8 == 88) {
			fprintf(out, "Using min(cw:%u,c2u:%u) bw:%s(%lu) with rtt:%lu gain:%u\n",
				bbr->flex2, bbr->flex1,
				display_bw(bbr->bw_inuse, 0),
				bbr->bw_inuse, bbr->rttProp, bbr->bbr_substate);
		} else if (bbr->flex8 == 89) {
			uint32_t buck_max, cur_buck;
			
			buck_max = (bbr->delRate & 0x00000000ffffffff);
			cur_buck = ((bbr->delRate >> 32) & 0x00000000ffffffff);
			fprintf(out, "Policed pacing at bw:%s (%lu) bucket_max:%u current_bucket:%u len:%u delay:%u\n",
				display_bw(bbr->bw_inuse, 0), bbr->bw_inuse,
				buck_max, cur_buck,
				bbr->flex2, bbr->flex1);
		} else if (bbr->flex8 == 99) {
			fprintf(out, "SRTT:%u overrides pacing time:%u minrtt:%u\n",
				bbr->flex2, bbr->flex1, bbr->pkts_out);
		} else {
			fprintf(out, "%d unknown?\n", bbr->flex8);
		}
	}
	break;
	case BBR_LOG_BBRUPD:
		/* PRR update */
		if (bbr->flex8 == 14) {
			uint32_t delta;

			delta = bbr->timeStamp - recovery_entered;
			fprintf(out, "EXIT RECOVERY cw_before_exit:%u rw:%u ssthresh:%u cw:%u NR:0x%x flight:%u (time to rec:%u) line:%u\n",
				bbr->pkts_out, l->tlb_snd_wnd,
				l->tlb_snd_ssthresh,
				l->tlb_snd_cwnd,
				bbr->use_lt_bw, bbr->inflight, delta,
				bbr->flex7);
		} else if (bbr->flex8 == 15) {
			recovery_entered = bbr->timeStamp;
			fprintf(out, "ENTER RECOVERY cw_before_entry:%u rw:%u ssthresh:%u cw:%u NR:0x%x flight:%u line:%u\n",
				bbr->pkts_out,l->tlb_snd_wnd,
				l->tlb_snd_ssthresh,
				l->tlb_snd_cwnd,
				bbr->use_lt_bw, bbr->inflight, bbr->flex7);
		} else {
			fprintf(out, "PRR UPDATE frm:%d out:%u recover_fs:%u sndcnt:%u del:%u sacked:%u holes:%u ssthresh:%u out:%u t_flags:0x%x NR:0x%x po:%d cw:%u\n",
				bbr->flex8,
				bbr->flex1,
				bbr->flex2,
				bbr->flex3,
				bbr->flex4,
				bbr->flex5, bbr->flex6,
				l->tlb_snd_ssthresh,
				(l->tlb_snd_max - l->tlb_snd_una), l->tlb_flags, bbr->use_lt_bw, bbr->pkts_out, l->tlb_snd_cwnd);
		}
		break;
	case TCP_LOG_LRO:
		dump_out_lro_log(l, bbr);
		break;
	case TCP_SACK_FILTER_RES:
		dump_sack_filter(bbr);
		break;
	case BBR_LOG_DOSEG_DONE:
		mask = get_timer_mask(bbr->flex4);
		{
			char sign;
			uint32_t chg;
			if (last_rwnd_at_out > l->tlb_snd_wnd) {
				sign = '-';
				chg = last_rwnd_at_out - l->tlb_snd_wnd;
			} else if (last_rwnd_at_out == l->tlb_snd_wnd) {
				sign = ' ';
				chg = 0;
			} else {
				sign = '+';
				chg = l->tlb_snd_wnd - last_rwnd_at_out;
			}
			fprintf(out, "do:%d np:%d wo:%d in_per:%d (ip:%d) tmrs:%s sndcnt:%u way_out:%d out:%u state:%u rw:%d (%c%u) nseg:%d\n",
				bbr->flex1,
				bbr->flex2,
				bbr->flex7,
				bbr->flex8,
				bbr->inhpts,
				mask, bbr->flex5,
				bbr->flex3,
				(l->tlb_snd_max - l->tlb_snd_una),
				l->tlb_state, l->tlb_snd_wnd,
				sign, chg, bbr->flex6);
			if (extra_print) {
				uint32_t rnd, lost;

				lost = (uint32_t)(bbr->bw_inuse & 0x00000000ffffffff);
				rnd = (uint32_t)((bbr->bw_inuse >> 32) & 0x00000000ffffffff);
				print_out_space(out);
				fprintf(out, "avail:%u inq:%u NR:0x%x must:%d snd_max_at:%u out_at_rto:%u flight:%u cw:%u\n",
					l->tlb_txbuf.tls_sb_acc,
					l->tlb_rxbuf.tls_sb_acc,
					bbr->use_lt_bw,
					bbr->pacing_gain, bbr->delivered, bbr->pkts_out,
					bbr->inflight,l->tlb_snd_cwnd);
				print_out_space(out);
				fprintf(out, "snd_una:%u snd_max:%u snd_nxt:%u lost:%u rnd:%u\n",
					l->tlb_snd_una, l->tlb_snd_max, l->tlb_snd_nxt, lost, rnd);
				print_out_space(out);
				fprintf(out, "snd_hiwat:%u rcv_hiwat:%u srtt:%u rbuf_cnt:%u\n",
					bbr->epoch,
					bbr->lt_epoch,
					bbr->lost, bbr->pkt_epoch);
			}
		}
		break;
	case TCP_LOG_FLOWEND:
		fprintf(out, " iss:%u snd_una:%u snd_max:%u (out:%u) start:%u rcv_nxt:%u avail:%u\n",
			l->tlb_iss,
			l->tlb_snd_una,
			l->tlb_snd_max,
			(l->tlb_snd_max - l->tlb_snd_una),
			l->tlb_starttime,
			l->tlb_rcv_nxt,
			l->tlb_txbuf.tls_sb_acc);
		break;
	case TCP_LOG_SOCKET_OPT:
		display_tcp_option(l);
		break;
	case BBR_LOG_PROGRESS:
		fprintf(out, " line:%d ticks:%u ack_time:%u max:%u event:%s (ip:%d) state:%u\n",
			bbr->flex1,
			bbr->flex2,
			bbr->flex3,
			bbr->flex4,
			get_progress_event(bbr->flex8), bbr->inhpts, l->tlb_state);
		break;
	case RACK_DSACK_HANDLING:
		/*
		 * Types of logs (flex8d value)
		 * 1 = dsack_persists reduced by 1 via T-O or fast recovery exit.
		 * 2 = a dsack round begins, persist is reset to 16.
		 * 3 = a dsack round ends
		 * 4 = Dsack option increases rack rtt flex5 is the srtt input, flex6 is thresh
		 * 5 = Socket option set changing the control flags rc_rack_tmr_std_based, rc_rack_use_dsack
		 * 6 = Final rack rtt, flex4 is srtt and flex6 is final limited thresh.
		 */
		fprintf(out, " - mod:%d ",
			bbr->flex8);
		if (bbr->flex8 == 1) {
			fprintf(out, "Persist reduced line:%u persists value:%d flags(SDR):0x%x\n",
				bbr->flex4, bbr->flex7, bbr->flex1);
		} else if (bbr->flex8 == 2) {
			fprintf(out, "Round begins line:%u persists value:%d flags(SDR):0x%x ends:%u num_dsack:%u\n",
				bbr->flex4, bbr->flex7, bbr->flex1, bbr->flex2, bbr->flex3);
		} else if (bbr->flex8 == 3) {
			fprintf(out, "Round ends line:%u persists value:%d flags(SDR):0x%x ends:%u num_dsack:%u\n",
				bbr->flex4, bbr->flex7, bbr->flex1, bbr->flex2, bbr->flex3);
		} else if (bbr->flex8 == 4) {
			fprintf(out, "Rack RTT increased by num_dsack:%u srtt:%u thresh:%u\n",
				bbr->flex3, bbr->flex5, bbr->flex6);
		} else if (bbr->flex8 == 5) {
			fprintf(out, "Rack DSACK line:%u option set flags(SDR) are now 0x%x\n",
				bbr->flex4,
				bbr->flex1);
		} else if (bbr->flex8 == 6) {
			fprintf(out, "Rack line:%u RTT num_dsack:%u srtt:%u final thresh:%u lost:%u round:%u\n",
				bbr->flex4,
				bbr->flex3, bbr->flex5, bbr->flex6, bbr->lt_epoch, bbr->epoch);
		} else if (bbr->flex8 == 7) {
			fprintf(out, "DSACK line:%u was TLP start:%u end:%u flags(SDR):0x%x num_dsack:%u \n",
				bbr->flex4,
				bbr->flex5,
				bbr->flex6,
				bbr->flex1,
				bbr->flex3);
		} else if (bbr->flex8 == 8) {
			fprintf(out, "TLP ACK/SACK line:%u start:%u end:%u flags(SDR):0x%x num_dsack:%u set valid flag\n",
				bbr->flex4,
				bbr->flex5,
				bbr->flex6,
				bbr->flex1,
				bbr->flex3);
		} else if (bbr->flex8 == 9) {
			fprintf(out, "TLP line:%u reached 1/2 start:%u end:%u are no longer valid flags(SDR):0x%x num_dsack:%u set valid flag\n",
				bbr->flex4,
				bbr->flex5,
				bbr->flex6,
				bbr->flex1,
				bbr->flex3);
		} else if (bbr->flex8 == 10) {
			fprintf(out, "TLP line:%d start:%u end:%u partial ack do not reset flags(SDR):0x%x num_dsack:%u set valid flag\n",
				bbr->flex4,
				bbr->flex5,
				bbr->flex6,
				bbr->flex1,
				bbr->flex3);
		} else if (bbr->flex8 == 11) {
			fprintf(out, "TLP line:%d start:%u end:%u expanded flags(SDR):0x%x num_dsack:%u set valid flag\n",
				bbr->flex4,
				bbr->flex5,
				bbr->flex6,
				bbr->flex1,
				bbr->flex3);
		} else {
			fprintf(out, "Unknown value %d\n", bbr->flex8);
		}
		break;
	case TCP_LOG_RTT:
		if (bbr->flex7 == 3) {
			fprintf(out, "TSTMP Echoed:%u idx:%u val:%u from:%lu\n",
				bbr->flex3,
				bbr->flex1,
				bbr->flex2,
				bbr->rttProp);
		} else if (bbr->flex7 == 2) {
			fprintf(out, "calcuate rtt:%u -- send_time:%u ack_time:%u frm:%d\n",
				bbr->flex1,
				bbr->flex2,
				bbr->flex3,
				bbr->flex4);
		} else {
			fprintf(out, " rtt:%u applied to srtt %u var %u t_flags:%x cw:%u t_flags2:0x%x\n",
				bbr->flex1,
				l->tlb_srtt,
				l->tlb_rttvar,
				l->tlb_flags, l->tlb_snd_cwnd, l->tlb_flags2);
			print_out_space(out);
			fprintf(out, "sd:%d ackcnt:%u sackcnt:%u nomove:%u move:%u sst:%u must:%d snd_max_at:%u out_at_rto:%u\n",
				bbr->flex8,
				bbr->flex2, bbr->flex3,
				bbr->flex4,
				bbr->flex5, l->tlb_snd_ssthresh,
				bbr->pacing_gain, bbr->delivered, bbr->pkts_out);
			print_out_space(out);
			fprintf(out, "rttcur:%u rack_rto_min:%u rack_rto_max:%u t_rttmin:%u rxtmacro:%lu defslop:%u rackslop:%u\n",
				bbr->flex6,
				bbr->applimited,
				bbr->epoch,
				bbr->lost, bbr->rttProp, bbr->pkt_epoch, bbr->lt_epoch);
		}
		break;
	case BBR_LOG_TIMERSTAR:
		clear_to_print = 1;
		if (show_all_messages) {
			const char *which_one;
			uint32_t lost, rnd;

			lost = (uint32_t)(bbr->bw_inuse & 0x00000000ffffffff);
			rnd = (uint32_t)((bbr->bw_inuse >> 32) & 0x00000000ffffffff);
			mask = get_timer_mask(bbr->flex3);
			if (bbr->flex8) {
				which_one = "pacer";
			} else {
				which_one =  "timer";
			}
			fprintf(out, "type:%s(%s:%u) srtt:%d (rttvar:%u * 4) rttmin:%u for %u(%u) cw:%u rw:%u (ip:%d) slot:%d frm:%d\n",
				mask,
				which_one, bbr->flex3,
				bbr->flex1, l->tlb_rttvar, bbr->lost,
				bbr->flex2, bbr->flex4,
				l->tlb_snd_cwnd, l->tlb_snd_wnd,
				bbr->inhpts,
				bbr->flex5, bbr->flex8);
			print_out_space(out);
			fprintf(out, "t_rxtcur:%u rxt_shift:%d state:%u (u:%u m:%u a:%u pers:%d) flight:%d must:%d snd_max_at:%u out_at_rto:%u\n",
				bbr->flex6, bbr->lt_epoch, l->tlb_state,
				l->tlb_snd_una, l->tlb_snd_max,
				l->tlb_txbuf.tls_sb_acc,
				bbr->flex7, bbr->inflight,
				bbr->pacing_gain, bbr->delivered, bbr->pkts_out);
			print_out_space(out);
			fprintf(out, "has_inited:%u roundends:%u defer:%u coll:%u lost:%u rnd:%u tp_flags2:0x%x\n",
				bbr->cwnd_gain, bbr->epoch,
				bbr->cwnd_gain,
				bbr->pkt_epoch, lost, rnd, bbr->applimited);
			if (bbr->flex3 & PACE_TMR_KEEP) {
				prev_sent_bytes = 0;
				prev_sent_time = 0;
				print_out_space(out);
				fprintf(out, "KEEP:Sent so far:%u\n",
					(l->tlb_snd_max - l->tlb_iss));
			}

		}
		break;
	case BBR_LOG_TIMERCANC:
		mask = get_timer_mask(bbr->flex3);
		if (bbr->flex8 == 1) {
			uint32_t rnd, lost;
			fprintf(out, "type:%s cw:%u rw:%u t_flags:0x%x (ip:%d) rm_frm_pacer:%d state:%u hpts_flgs:%d line:%d t_flags2:0x%x\n",
				mask,
				l->tlb_snd_cwnd, l->tlb_snd_wnd,
				l->tlb_flags,
				bbr->inhpts,
				bbr->flex7, l->tlb_state,
				bbr->flex3, bbr->flex1,
				l->tlb_flags2
				);
			print_out_space(out);
			rnd = (uint32_t)((bbr->bw_inuse >> 32) & 0x00000000ffffffff);
			lost = (uint32_t)(bbr->bw_inuse  & 0x00000000ffffffff);
			fprintf(out, "last_output_to:%u now:%u prr:%u sst:%u flight:%u rnd:%u lost:%u\n",
				bbr->flex2, bbr->flex4, bbr->flex5,
				l->tlb_snd_ssthresh, bbr->inflight, rnd, lost);
		} else if (bbr->flex8 == 98) {
			fprintf(out, "MOD:98 TLP min thresh:%u time_since:%u tstmp_u:%u last_txt:%u rsm:%u srtt:%u idx:%d\n",
				bbr->flex1,
				bbr->flex2,
				bbr->flex3,
				bbr->flex4,
				bbr->flex5,
				bbr->flex6,
				bbr->flex7);

		} else if (bbr->flex8 == 99) {
			fprintf(out, "MOD:99 TLP min thresh:%u time_since:%u tstmp_u:%u last_txt:%u rsm:%u srtt:%u idx:%d\n",
				bbr->flex1,
				bbr->flex2,
				bbr->flex3,
				bbr->flex4,
				bbr->flex5,
				bbr->flex6,
				bbr->flex7);
		} else {
			fprintf(out, "Unknown timer cancel mod:%d\n", bbr->flex8);
		}
		break;
	case BBR_LOG_TO_PROCESS:
		if (show_all_messages) {
			int32_t ret;

			ret = (int32_t)bbr->flex2;
			if (ret >= 0) {
				mask = get_timer_mask(bbr->flex1);
				fprintf(out, " timers %s return %d expires:%u state:%u prr:%u\n",
					mask, bbr->flex2,
					bbr->flex3, l->tlb_state,
					bbr->flex6);
			} else {
				/* A early to */
				mask = get_timer_mask(bbr->flex4);
				if (ret == -1) {
					fprintf(out, "Output in progress tmr %s state:%u flags:%x prr:%u\n",
						mask, l->tlb_state, l->tlb_flags, bbr->flex6);
				} else if (ret == -2) {
					fprintf(out, "Not pacer calling for tmr %s state:%u prr:%u\n",
						mask, l->tlb_state, bbr->flex6);
				} else {
					fprintf(out, "Not enough time yet tmr %s left:%d reinsert cts:%u exp:%u state:%u prr:%u\n",
						mask, bbr->flex1, bbr->flex5, bbr->flex3, l->tlb_state, bbr->flex6);
				}
			}
			if (extra_print) {
				print_out_space(out);
				fprintf(out, "must:%d snd_max_at:%u out_at_rto:%u\n",
					bbr->pacing_gain, bbr->delivered, bbr->pkts_out);
			}
		}
		break;
	case BBR_LOG_BBRSND:
		fprintf(out, "slot:%u (ip:%d) state:%u t_flags:0x%x prr:%d a_o_s:%u line:%u\n",
			bbr->flex1, bbr->inhpts, l->tlb_state, l->tlb_flags, bbr->flex2, bbr->flex5, bbr->flex6);
		break;
	case BBR_LOG_JUSTRET:
	{
		const char *reascode;

		last_cwnd_to_use = bbr->lt_epoch;
		reascode = get_jr_reason(bbr->flex4);
		fprintf(out, "slot:%u (ip:%d pc:%d) in_persist:%d avail:%u scw:%u rw:%u out:%u state:%u sndcnt:%d cw:%u reas:%s\n",
			bbr->flex1, bbr->inhpts,
			bbr->flex7, bbr->flex8,
			l->tlb_txbuf.tls_sb_acc,
			bbr->lt_epoch,
			l->tlb_snd_wnd,
			(l->tlb_snd_max - l->tlb_snd_una),
			l->tlb_state, bbr->flex5, l->tlb_snd_cwnd, reascode);
		if (extra_print) {
			print_out_space(out);
			mask = get_timer_mask(bbr->flex2);
			fprintf(out, "snd_una:%u snd_nxt:%u snd_max:%u sb_off:%u tmr:0x%x (%s) t_flags:0x%x cg:%u pg:%u\n",
				l->tlb_snd_una, l->tlb_snd_nxt, l->tlb_snd_max,
				(l->tlb_snd_nxt - l->tlb_snd_una), bbr->flex2, mask,
				l->tlb_flags, bbr->cwnd_gain, bbr->pacing_gain);
		}
	}
	break;
	case  TCP_LOG_USERSEND:
		fprintf(out, "avail:%u pending:%u snd_una:%u snd_max:%u out:%u t_flags:0x%x (ip:%d)\n",
			l->tlb_txbuf.tls_sb_acc,
			l->tlb_txbuf.tls_sb_ccc,
			l->tlb_snd_una,
			l->tlb_snd_max,
			(l->tlb_snd_max - l->tlb_snd_una),
			l->tlb_flags, bbr->inhpts);
		break;
	case TCP_LOG_SENDFILE:
		handle_sendfile_log_entry(l);
		break;
	case BBR_LOG_HPTSDIAG:
		/*
		 * The pacer diag abuses 3 bbr fields to transfer
		 * all insert pacer information.
		 */
		if (show_all_messages) {
			show_pacer_diag(bbr);
		}
		break;
	case TCP_LOG_REQ_T:
		tcp_display_http_log(l, bbr);
		break;
	case TCP_LOG_SB_WAKE:
		tcp_display_wakeup(l, bbr);
		break;
	case TCP_HYSTART:
		show_hystart(l, bbr);
		break;
	case TCP_LOG_IN:
	{
		uint32_t lro_time;
		int off_len;
		uint16_t rw_in;
		uint32_t acks;
		uint32_t snd_una;
		const char *ackstate, *datastate;
		const char *ack_type;
		const char *mflag_type;
		const char *tflags;
		int have_ack;

		if (bbr->flex7 == 1) {
			ack_type = "Compressed";
		} else if (bbr->flex7 == 2) {
			ack_type = "Normal";
		} else {
			ack_type = "Unkown";
		}
		snd_una = l->tlb_snd_una;
		last_rwnd_at_out = l->tlb_snd_wnd;
		if (th) {
			have_ack = th->th_flags & TH_ACK;
			th_ack = ntohl(th->th_ack);
			th_seq = ntohl(th->th_seq);
			if (irs_set == 0) {
				irs = th_seq;
				irs_set = 1;
			}
			if (use_relative_seq) {
				th_seq -= irs;
				th_ack -= l->tlb_iss;
				snd_una -= l->tlb_iss;
			}
			tflags = translate_flags(tcp_get_flags(th));
			rw_in = ntohs(th->th_win);
			off_len = th->th_off << 2;
		} else {
			have_ack = 0;
			off_len = 0;
			th_ack = 0xbadbad;
			tflags = "bad";
			th_seq = 0xbadbad;
		}
		if (bbr->flex3 & M_TSTMP) {
			lro_time = bbr->lt_epoch;
			mflag_type = "HDWR STAMP";
		}
		else if (bbr->flex3 & M_TSTMP_LRO) {
			lro_time = bbr->flex5;
			mflag_type = "LRO  STAMP";
		} else {
			lro_time = l_timeStamp;
			mflag_type = "NO  STAMP";
		}
		if (!have_ack) {
			acks = 0;
			ackstate = "none";
		} else if (SEQ_GT(th_ack, snd_una)) {
			acks = th_ack - snd_una;
			total_log_in += acks;
			ackstate = "new";
		} else {
			acks = 0;
			if (th_ack ==  snd_una)
				ackstate = "new";
			else
				ackstate = "old";
		}
		if (l->tlb_len) {
			if (SEQ_LT(th_seq, l->tlb_rcv_nxt))
				datastate = "old-data";
			else
				datastate = "new-data";
		} else {
			datastate = "no-data";
		}
		if (rack_last_in_set == 0) {
			rack_last_in = l_timeStamp;
			rack_last_in_set = 1;
		}
		if(rack_arr_in_set == 0) {
			rack_arr_in = lro_time;
			rack_arr_in_set = 1;
		}
		fprintf(out, "Ack:%s %u (%s) off:%u out:%u lenin:%u avail:%u cw:%u rw:%u una:%u ack:%u t_flags:0x%x(%s,%s)\n",
			ack_type,
			acks,
			tflags,
			off_len,
			(l->tlb_snd_max - l->tlb_snd_una),
			l->tlb_len,
			l->tlb_txbuf.tls_sb_acc,
			l->tlb_snd_cwnd,
			l->tlb_snd_wnd,
			snd_una,
			th_ack, l->tlb_flags,
			ackstate, datastate);
		print_out_space(out);
		fprintf(out, "(ip:%d) state:%d t_flags:%x prr:%u t_flags2:0x%x\n",
			bbr->inhpts, l->tlb_state, l->tlb_flags, bbr->flex1,
			l->tlb_flags2);
		rack_sab_sum += (lro_time - rack_last_in);
		if (extra_print) {
			print_out_space(out);
			mask = get_timer_mask(bbr->flex4);
			fprintf(out, "mflags:0x%x nxt_pkt:%d hwts=0x%x ats:0x%x hpts_flags:%s(%x) mapa:%u NR:0x%x\n",
				bbr->flex3,
				bbr->flex8,
				bbr->lt_epoch,
				bbr->flex5,
				mask,
				bbr->flex4,
				bbr->flex2, bbr->use_lt_bw);
			print_out_space(out);
			fprintf(out, "rcv_buf cc:%u snd_buf cc:%u rw_in:%u out:%u inflight:%u\n",
				l->tlb_rxbuf.tls_sb_acc, l->tlb_txbuf.tls_sb_acc, rw_in,
				(l->tlb_snd_max - l->tlb_snd_una),
				bbr->inflight
				);
			print_out_space(out);
			fprintf(out, " th_ack:%u pe:%u th_seq:%u rcv_nxt:%u ssthresh:%u\n",
				th_ack, bbr->pkt_epoch, th_seq, l->tlb_rcv_nxt, l->tlb_snd_ssthresh);
			print_out_space(out);
			if (lro_flush_time) {
				fprintf(out, " snd_una:%u snd_max:%u iss:%u sabsum:%lu mflags:%s arrvtsmp:%u\n",
					snd_una,
					(use_relative_seq == 0 ? l->tlb_snd_max : (l->tlb_snd_max - l->tlb_iss)),
					l->tlb_iss, rack_sab_sum, mflag_type, lro_time);
				print_out_space(out);
				fprintf(out,"flush_ts:%u (delay:%u) rec:%u (spa:%u ar_spa:%u)\n",
					lro_flush_time,
					(lro_flush_time - lro_time),
					l->tlb_snd_recover,
					(lro_time - rack_arr_in),
					(l_timeStamp - rack_last_in));
			} else {
				fprintf(out, " snd_una:%u snd_max:%u iss:%u sabsum:%lu arrvtsmp:%u rec:%u (spa:%u ar_spa:%u)\n",
					snd_una,
					l->tlb_snd_max,
					l->tlb_iss, rack_sab_sum, lro_time,
					l->tlb_snd_recover,
					(lro_time - rack_arr_in),
					(l_timeStamp - rack_last_in));
			}
			print_out_space(out);
			fprintf(out, "avail:%u inq:%u COcR:0x%x (ticks:%u start_tm:%u ago:%u) ack_type:%u\n",
				l->tlb_txbuf.tls_sb_acc,
				l->tlb_rxbuf.tls_sb_acc,
				bbr->applimited,
				l->tlb_starttime,
				l->tlb_ticks, (l->tlb_ticks - l->tlb_starttime), bbr->cwnd_gain);
			if (bbr->flex8) {
				struct timeval reqt, delta;

				print_out_space(out);
				fprintf(out, " tm:%lu [start:%lu ",
					bbr->rttProp,
					bbr->cur_del_rate);
				if (bbr->flex8 & 1) {
					/* Open range req */
					fprintf(out, " end:- ]");
				} else if (bbr->flex8 & 2) {
					/* Closed range req */
					fprintf(out, " end:%lu ]",
						bbr->bw_inuse);
				} else
					fprintf(out, " ??]");
				fprintf(out, " sseq:%u",
					bbr->flex6);
				if (bbr->flex8 & 4) {
					/* has completed */
					fprintf(out, " endseq:%u ",
						bbr->epoch);
				} else {
					/* send file still working on it */
					fprintf(out, " endseq: - ");
				}
				delta.tv_sec = 0;
				delta.tv_usec = 0;
				reqt.tv_sec = bbr->pkt_epoch;
				reqt.tv_usec = bbr->delivered;
				if (reqt.tv_sec) {
					if (timercmp(&l->tlb_tv, &reqt, >)) {
						timersub(&l->tlb_tv, &reqt, &delta);
					}
				}
				fprintf(out, "sec:%u usec:%u (ago:%lu.%6.6lu)\n",
					bbr->pkt_epoch,
					bbr->delivered,
					delta.tv_sec, delta.tv_usec);
			}
			optptr = (const uint8_t *)th;
			optptr += sizeof(struct tcphdr);
			process_options(&to, th, optptr);
			if (to.to_flags & TOF_TS) {
				print_out_space(out);
				fprintf(out, "TSTMP VAL:%u ECHO:%u\n",
					to.to_tsval, to.to_tsecr);
			}
			if (to.to_flags & TOF_SACK) {
				print_sack_blocks(&to, th_ack);
			}
		}
		rack_last_in = l_timeStamp;
		rack_arr_in = lro_time;
		if (th && (th->th_flags & TH_RST) && (ann_end == 0)) {
			ann_end = 1;
			fprintf(out, "***Flow Ends sent %u bytes\n", (l->tlb_snd_max - l->tlb_iss));
		}
		break;
	}
	case TCP_LOG_REASS:
		print_tcp_log_reass(l, bbr);
		break;
	case TCP_HDWR_PACE_SIZE:
		print_pace_size(l, bbr);
		break;
	case TCP_LOG_CONNEND:
		display_connection_end(l, bbr);
		break;
	case BBR_LOG_SETTINGS_CHG:
	{
		const char *foo;

		if (bbr->flex8 == 1)
			foo = "retransmission";
		else if(bbr->flex8 == 2)
			foo = "clear count";
		else if (bbr->flex8 == 3)
			foo = "raise count";
		else
			foo = "UNKNOWN";
		if (bbr->flex8 == 1)
			fprintf(out, " RACK RTR Reason:%s (%u) start:%u end:%u dupack:%u flags:0x%x must:%d snd_max_at:%u out_at_rto:%u\n",
				foo,
				bbr->flex8,
				bbr->flex5, bbr->flex6,
				bbr->flex4, bbr->flex3,
				bbr->pacing_gain, bbr->delivered, bbr->pkts_out);
		else
			fprintf(out, " RACK RTR Reason:%s (%u) start:%u end:%u dupack:%u flags:0x%x line:%d must:%d snd_max_at:%u out_at_rto:%u\n",
				foo,
				bbr->flex8,
				bbr->flex5, bbr->flex6,
				bbr->flex4, bbr->flex3, bbr->flex1,
				bbr->pacing_gain, bbr->delivered, bbr->pkts_out);

		break;
	}
	case TCP_LOG_MAPCHG:
		display_map_chg(bbr);
		break;
	case TCP_LOG_FSB:
		fprintf(out, " mod:%d err:%d flags:0x%x rsm:%d ipoptlen:%d rcv_nsack:%d optlen:%d fsb_init:%d fo:%d orig_len:%d len:%d line:%u\n",
			bbr->cwnd_gain,
			bbr->flex1, bbr->flex2, bbr->flex3,
			bbr->flex4, bbr->flex5, bbr->flex7,
			bbr->flex8,
			bbr->applimited,
			bbr->pkts_out,
			bbr->lt_epoch, bbr->delivered);
		break;
	case TCP_CHG_QUERY:
		display_change_query(l, bbr);
		break;
	case TCP_RACK_LOG_COLLAPSE:
		if (bbr->flex8 == 1) {
			fprintf(out, "-- Window collapsed at seq:%u snd_max:%u (lost %u)\n",
				bbr->flex3, l->tlb_snd_max, (l->tlb_snd_max - bbr->flex3));
		} else if (bbr->flex8 == 0) {
			fprintf(out, "-- Window uncollapsed -- marked:%u split:%u out:%u rw:%u from line:%u col:%u must:%u\n",
				bbr->flex1, bbr->flex2,
				bbr->flex3,
				l->tlb_snd_wnd,
				bbr->flex4,
				bbr->flex7,
				bbr->flex5);
		} else if (bbr->flex8 == 3) {
			fprintf(out, "-- Splitting rsm->r_start:%u rsm->r_end:%u flags:0x%x at maxseq:%u snd_max:%u (rsm:0x%lx)\n",
				bbr->flex1, bbr->flex2, bbr->flex6,
				bbr->flex3, l->tlb_snd_max, bbr->rttProp);
		} else if (bbr->flex8 == 4) {
			fprintf(out, "-- Mark rsm->r_start:%u rsm->r_end:%u (len:%u) flags:0x%x un-collapsed (rsm:0x%lx)\n",
				bbr->flex1, bbr->flex2, (bbr->flex2 - bbr->flex1),
				bbr->flex6, bbr->rttProp);
		} else if (bbr->flex8 == 5) {
			fprintf(out, "--RSM RXT rsm->r_start:%u rsm->r_end:%u (len:%u) flags:0x%x (rsm:0x%lx)\n",
				bbr->flex1, bbr->flex2,
				(bbr->flex2 - bbr->flex1),
				bbr->flex6, bbr->rttProp);
		} else if ((bbr->flex8 == 6) || (bbr->flex8 == 7)) {
			fprintf(out, "--RSM RXT %s timersm->r_start:%u time_passed:%u thresh:%u flags:0x%x (rsm:0x%lx)\n",
				((bbr->flex8 == 6) ? "Enough" : "Not enough"),
				bbr->flex1, bbr->flex2, bbr->flex3,
				bbr->flex6, bbr->rttProp);
		} else {
			fprintf(out, "-- Unknown val in flex8 %d\n", bbr->flex8);
		}
		break;
	case TCP_RACK_TP_TRIGGERED:
		display_tp_trigger(l);
		break;
	case TCP_HYBRID_PACING_LOG:
		display_hybrid_pacing(l, bbr);
		break;
	case TCP_LOG_PRU:
		display_pru(l);
		break;
	case TCP_LOG_RTO:
		display_tcp_rto(l);
		break;
	case TCP_LOG_OUT:
	{
		const char *rtr;
		if (th) {
			th_ack = ntohl(th->th_ack);
			th_seq = ntohl(th->th_seq);
			if (use_relative_seq) {
				th_seq -= l->tlb_iss;
			}
		} else {
			th_ack = 0xbadbad;
			th_seq = 0xbadbad;
		}
		rtr = " ";
		last_cwnd_to_use = bbr->lt_epoch;
		if ((th_seq == l->tlb_snd_max) &&
		    (bbr->flex8 == 1)) {
			fprintf(stderr, "Warning sn:%u packet marked retransmission impossible seq == snd_max\n",
				l->tlb_sn);
		} else if (bbr->flex8) {
			if (bbr->flex8 == 2) {
				rtr = "T*";
			} else if (bbr->flex8 == 3) {
				rtr = "T";
			} else if (bbr->flex8 == 4) {
				rtr = "R";
			} else
				rtr = "* ";
			if ((bbr->flex8 == 1) ||
			    (bbr->flex8  == 2)) {
				lost_rack_count += l->tlb_len;
			}
		} else {
			total_log_out += l->tlb_len;
		}
		fprintf(out, "Sent(%d) %u:%u%s (%s fas:%u bas:%u) bw:%s(%lu) avail:%d cw:%u scw:%u rw:%u flt:%u (spo:%u ip:%d)\n",
			l->tlb_errno,
			th_seq, l->tlb_len, rtr,
			translate_flags(tcp_get_flags(th)), bbr->flex5,  bbr->bbr_substate,
			display_bw(bbr->bw_inuse, 0), bbr->bw_inuse,
			l->tlb_txbuf.tls_sb_acc,
			l->tlb_snd_cwnd,
			bbr->lt_epoch,
			l->tlb_snd_wnd, bbr->inflight,
			(time_to_use - rack_last_out), bbr->inhpts);
		if (extra_print) {
			print_out_space(out);
			fprintf(out, "state:%u srtt:%u pace min:%u max:%u t_flags:0x%x orig_len:%u mark:%u flight:%u inq:%u state:%d gp:%s (%lu) gain:%u\n",
				l->tlb_state, l->tlb_srtt,
				bbr->flex2, bbr->flex3, l->tlb_flags, bbr->flex4, bbr->flex7, bbr->inflight,
				l->tlb_rxbuf.tls_sb_acc, l->tlb_state,
				display_bw(bbr->cur_del_rate, 0), bbr->cur_del_rate, bbr->pacing_gain);
			print_out_space(out);
			fprintf(out, "Min seg:%u Max seg:%u agg_delay:%u agg_early:%u TH_ACK:%u out:%u sst:%u iss:%u sal:%d sndcnt:%d t_maxseg:%u\n",
				bbr->flex2, bbr->flex3, bbr->applimited, bbr->flex6, th_ack,
				(l->tlb_snd_max - l->tlb_snd_una),
				l->tlb_snd_ssthresh, l->tlb_iss, bbr->delivered, bbr->flex1, bbr->pkts_out);
			print_out_space(out);
			fprintf(out, "snd_max:%u snd_una:%u snd_nxt:%u flex8:%u rsm:0x%lx flag|MS:0x%lx\n",
				l->tlb_snd_max, l->tlb_snd_una,
				l->tlb_snd_nxt,
				bbr->flex8,
				bbr->rttProp, bbr->delRate);
			if (clear_to_print) {
				if (prev_sent_time && prev_sent_bytes && (l->tlb_len > 0)) {
					uint64_t bw, now, t, oh;
					
					now = tcp_tv_to_lusectick(&l->tlb_tv);
					bw = prev_sent_bytes;
					oh = bw / (uint64_t)bbr->flex2;
					if (oh == 0)
						oh = 1;
					if (v6) {
						oh *= (40 + 40 + 14);
					} else {
						oh *= (20 + 40 + 14);
					}
					bw += oh;
					bw *= 1000000;
					t = now - prev_sent_time;
					if (t) {
						bw /= t;
						print_out_space(out);
						fprintf(out, "Paced at %s [%lu] pb:%u tim:%lu sn:%u oh:%lu\n",
							display_bw(bw, 0),
							bw, prev_sent_bytes,
							t,
							prev_sn, oh);
					} else {
						print_out_space(out);
						fprintf(out, "Paced at -- No delay since last send -- rate is infinity sn:%u\n", l->tlb_sn);
					}
					clear_to_print = 0;
				} else {
					print_out_space(out);
					if (l->tlb_len > 0) 
						fprintf(out, "Paced at -- No B/W (idle) yet sn:%u sending:%u\n", l->tlb_sn, l->tlb_len);
					else
						fprintf(out, "Paced at -- No B/W sending:%u bytes\n", l->tlb_len);
					clear_to_print = 0;
				}
				if (l->tlb_len) {
					prev_sent_bytes = l->tlb_len;
					prev_sent_time = tcp_tv_to_lusectick(&l->tlb_tv);
					prev_sn = l->tlb_sn;
				}
			} else {
				prev_sent_bytes += l->tlb_len;
			}
			if (th) {
				optptr = (const uint8_t *)th;
				optptr += sizeof(struct tcphdr);
				process_options(&to, th, optptr);
				if (to.to_flags & TOF_TS) {
					print_out_space(out);
					fprintf(out, "TSTMP VAL:%u ECHO:%u\n",
						to.to_tsval, to.to_tsecr);
				}
				if (to.to_flags & TOF_SACK) {
					print_sack_blocks(&to, th_ack);
				}
			} else {
				print_out_space(out);
				fprintf(out, "**** th is null\n");
			}
		}
		rack_last_out = time_to_use;
		calc = th_seq + l->tlb_len;
		if (SEQ_GT(calc, next_seq)) {
			next_seq = calc;
		}
		if (th && (th->th_flags & TH_FIN) && (ann_end == 0)) {
			ann_end = 1;
			fprintf(out, "***Flow Ends sent %u bytes\n", (l->tlb_snd_max - l->tlb_iss));
		}
		break;
	}
	case BBR_LOG_RTT_SHRINKS:
		if (bbr->flex8 == 0) {
			fprintf(out, "INIT \n");
		} else if (bbr->flex8 == 1) {
			int32_t rttdif;
			uint32_t minrtt, maxrtt;

			maxrtt = ((bbr->cur_del_rate >> 32) & 0x00000000ffffffff);
			minrtt = (bbr->cur_del_rate & 0x00000000ffffffff);
			rttdif = (int32_t)bbr->pkts_out;
			fprintf(out, "NEW Low RTT flight:%u ortt:%u newrtt:%u (%u) (%u ago min:%u max:%u) TIMELYdiff:%d HFGIS:0x%x\n",
				bbr->inflight,
				bbr->flex5, bbr->lost, (bbr->flex5 - bbr->lost),
				(l_timeStamp - bbr->pkt_epoch),
				minrtt, maxrtt,
				rttdif, bbr->flex6);
			gp_lower_rtt = l_timeStamp;
		} else if (bbr->flex8 == 2) {
			int32_t rttdif;
			uint32_t entry_rtt;

			entry_rtt = (bbr->rttProp & 0x00000000ffffffff);
			rttdif = (int32_t)bbr->pkts_out;
			fprintf(out, "EXIT PROBERTT flight:%u gpbw:%s(%lu) gpsrtt:%u new_low_rtt:%u stayed:%u TIMELYdiff:%d goal:%u entered:%u starts:%u cw:%u entry:%u\n",
				bbr->inflight,
				display_bw(bbr->delRate, 0),
				bbr->delRate,
				bbr->lt_epoch,
				bbr->flex5,
				(l_timeStamp - bbr->applimited),
				rttdif, bbr->delivered,
				bbr->applimited, bbr->flex2,
				l->tlb_snd_cwnd, entry_rtt);
			gp_lower_rtt = l_timeStamp;
		} else if (bbr->flex8 == 3) {
			int32_t rttdif;

			rttdif = (int32_t)bbr->pkts_out;
			fprintf(out, "ENTER PROBERTT flight:%u gain:%u gpbw:%s gpsrtt:%u cur_low_rtt:%u TIMELYdiff:%d (last shrink %u ago) goal:%u HFGIS:0x%x\n",
				bbr->inflight,
				bbr->flex7,
				display_bw(bbr->delRate, 0),
				bbr->lt_epoch,
				bbr->flex5,
				rttdif,
				(l_timeStamp - gp_lower_rtt), bbr->delivered, bbr->flex6
				);
		} else if (bbr->flex8 == 4) {
			/* Reached target or time */
			fprintf(out, "REACHED TARGET flight:%u goal:%u <or> in:%u + mul * gp_srtt:%u TIMELY prev_gp_srtt:%u\n",
				bbr->inflight,
				bbr->delivered,
				(l_timeStamp - bbr->applimited),
				bbr->epoch, bbr->lt_epoch);
		} else if (bbr->flex8 == 5) {
			fprintf(out, "Highly Buffered Path high_rtt:%u low_rtt:%u\n",
				bbr->flex5, bbr->flex1);
		} else if (bbr->flex8 == 6) {
			fprintf(out, "No Backoff gp_srtt:%u < (min:%u + ((min%u * mul:%u) / div:%u))\n",
				bbr->epoch,
				bbr->lost, bbr->lost, bbr->flex5, bbr->flex1);
		} else if (bbr->flex8 == 7) {
			uint32_t entry_rtt;

			entry_rtt = (bbr->rttProp & 0x00000000ffffffff);
			fprintf(out, "SAFETY PROBERTT flight:%u gpbw:%s(%lu) gpsrtt:%u new_low_rtt:%u stayed:%u goal:%u entered:%u starts:%u cw:%u entry:%u\n",
				bbr->inflight,
				display_bw(bbr->delRate, 0),
				bbr->delRate,
				bbr->lt_epoch,
				bbr->flex5,
				(l_timeStamp - bbr->applimited),
				bbr->delivered,
				bbr->applimited, bbr->flex2,
				l->tlb_snd_cwnd, entry_rtt);
		} else {

			fprintf(out, "UNKNOWN flex8:%d\n",
				bbr->flex8);
		}
		if (extra_print) {
			uint32_t highrtt, lowrtt;

			highrtt = (bbr->cur_del_rate >> 32) & 0x00000000ffffffff;
			lowrtt = bbr->cur_del_rate & 0x00000000ffffffff;
			print_out_space(out);
			fprintf(out, "H FGIS:0x%x low:%u high:%u\n",
				bbr->flex6,
				highrtt, lowrtt);
		}
		break;
	case TCP_TIMELY_WORK:

		if (bbr->flex8 == 1) {
			char *gpbw;

			gpbw = display_bw(bbr->rttProp, 0);
			fprintf(out,
				"Timely Increase GP mask:0x%x ss:%u ca:%u rec:%u incr_per:%lu [lup:%d ldw:%d ASIR:0x%x] bw:%s(%lu) DRSC:0x%x Line:%u\n",
				bbr->flex1,
				bbr->flex4,
				bbr->flex5,
				bbr->flex6, bbr->cur_del_rate,
				bbr->flex3, bbr->flex7, bbr->flex2, gpbw, bbr->rttProp, bbr->cwnd_gain, bbr->pkt_epoch
				);
		} else if (bbr->flex8 == 2) {
			char *gpbw;
			uint32_t ca_red, ss_red, rec_red;

			ca_red = (bbr->bw_inuse & 0x00000000ffffffff);
			ss_red = ((bbr->bw_inuse >> 32) & 0x00000000ffffffff);
			rec_red = (bbr->cur_del_rate & 0x00000000ffffffff);
			gpbw = display_bw(bbr->rttProp, 0);
			fprintf(out,
				"Timely Decrease GP mask:0x%x ss:%u ca:%u rec:%u redca:%u redss:%u redrec:%u [lup:%d ldw:%d ASIR:0x%x] bw:%s(%lu) DRSC:0x%x Line:%u\n",
				bbr->flex1,
				bbr->flex4,
				bbr->flex5,
				bbr->flex6,
				ca_red, ss_red, rec_red,
				bbr->flex3, bbr->flex7, bbr->flex2,
				gpbw, bbr->rttProp, bbr->cwnd_gain, bbr->pkt_epoch
				);
		} else if (bbr->flex8 == 3) {
			char *gbw, *lbw, *ubw;

			lbw = display_bw(bbr->delRate, 1);
			gbw = display_bw(bbr->cur_del_rate, 1);
			ubw = display_bw(bbr->bw_inuse, 1);
			fprintf(out,
				"Timely comparison timely:%s(%u) low_bnd:%s(%lu) < cur_bw:%s(%lu) < up_bnd:%s(%lu) [lup:%d ldw:%d ASIR:0x%x] Line:%d\n",
				(bbr->flex1 ? "DEC" : "INC"), bbr->flex1,
				lbw, bbr->delRate,
				gbw, bbr->cur_del_rate,
				ubw, bbr->bw_inuse,
				bbr->flex3, bbr->flex7, bbr->flex2, bbr->pkt_epoch
				);
			if (gbw)
				free(gbw);
			if (ubw)
				free(ubw);
			if (lbw)
				free(lbw);
		} else if (bbr->flex8 == 4) {
			uint32_t rtt;
			uint32_t threshold, lprev_rtt;

			threshold = ((bbr->cur_del_rate >> 32) & 0x00000000ffffffff);
			lprev_rtt = (bbr->cur_del_rate & 0x00000000ffffffff);
			rtt = (uint32_t)(bbr->bw_inuse & 0x00000000ffffffff);
			my_rtt_diff = (int32_t)rtt;
			rtt = (uint32_t)((bbr->bw_inuse >> 32) & 0x00000000ffffffff);
			fprintf(out,
				"Timely calc timely:%s(%u) (rtt above max) rtt:%u > threshold:%u low_rtt:%lu prtt:%u rtt_diff:%d Line:%u\n",
				(bbr->flex1 ? "DEC" : "INC"), bbr->flex1,
				rtt, threshold,
				bbr->delRate,
				lprev_rtt, my_rtt_diff, bbr->pkt_epoch);
			if (extra_print) {
				print_out_space(out);
				fprintf(out,
					"TIMELY_WORK flight:%u cwtu:%u sst:%u gpsrtt:%u p_gp_srtt:%u lost:%u DRSC:0x%x\n",
					bbr->inflight,
					last_cwnd_to_use, l->tlb_snd_ssthresh, bbr->epoch,
					bbr->lt_epoch, bbr->lost, bbr->cwnd_gain);
			}
		} else if (bbr->flex8 == 5) {
			uint32_t rtt;
			uint32_t lprev_rtt;
			uint32_t threshold;

			threshold = ((bbr->cur_del_rate >> 32) & 0x00000000ffffffff);
			lprev_rtt = (bbr->cur_del_rate & 0x00000000ffffffff);
			rtt = (uint32_t)(bbr->bw_inuse & 0x00000000ffffffff);
			my_rtt_diff = (int32_t)rtt;
			rtt = (uint32_t)((bbr->bw_inuse >> 32) & 0x00000000ffffffff);
			fprintf(out,
				"Timely calc timely:%s(%d) (rtt below min) rtt:%u <  threshold:%u low_rtt:%lu prtt:%u rtt_diff:%d Line:%u\n",
				(bbr->flex1 ? "DEC": "INC"), bbr->flex1,
				rtt, threshold,
				bbr->delRate,
				lprev_rtt, my_rtt_diff, bbr->pkt_epoch);
			if (extra_print) {
				print_out_space(out);
				fprintf(out,
					"TIMELY_WORK flight:%u cwtu:%u sst:%u gpsrtt:%u p_gp_srtt:%u lost:%u DRSC:0x%x\n",
					bbr->inflight,
					last_cwnd_to_use, l->tlb_snd_ssthresh,
					bbr->epoch, bbr->lt_epoch, bbr->lost, bbr->cwnd_gain);
			}
		} else if ((bbr->flex8 == 6) || (bbr->flex8 == 7)) {
			uint32_t rtt;
			uint32_t lprev_rtt;

			lprev_rtt = (bbr->cur_del_rate & 0x00000000ffffffff);
			rtt = (uint32_t)(bbr->bw_inuse & 0x00000000ffffffff);
			my_rtt_diff = (int32_t)rtt;
			rtt = (uint32_t)((bbr->bw_inuse >> 32) & 0x00000000ffffffff);
			fprintf(out,
				"Timely calc timely:%s(%d) (gradient based) rtt:%u low_rtt:%lu prtt:%u rtt_diff:%d Line:%u\n",
				(bbr->flex1 ? "DEC": "INC"), bbr->flex1,
				rtt,
				bbr->delRate,
				lprev_rtt, my_rtt_diff, bbr->pkt_epoch);
			if (extra_print) {
				print_out_space(out);
				fprintf(out,
					"TIMELY_WORK flight:%u cwtu:%u sst:%u gpsrtt:%u p_gp_srtt:%u lost:%u DRSC:0x%x\n",
					bbr->inflight,
					last_cwnd_to_use, l->tlb_snd_ssthresh,
					bbr->epoch, bbr->lt_epoch, bbr->lost, bbr->cwnd_gain);
			}
		} else if ((bbr->flex8 == 8) || (bbr->flex8 == 9)) {
			char *cbw, *cr, *mr;
			const char *str1 = "above max pacing rate (no increment)";
			const char *str2 = "below max pacing rate (may increment)";

			cbw = display_bw(bbr->cur_del_rate, 1);
			cr = display_bw(bbr->delRate, 1);
			mr = display_bw(bbr->bw_inuse, 1);
			fprintf(out,
				"Timely %s mul:%d cur_bw:%s(%lu) cur_rate:%s(%lu) max_rate:%s(%lu) Line:%u\n",
				((bbr->flex8 == 8) ? str1 : str2),
				bbr->flex1,
				cbw, bbr->cur_del_rate,
				cr, bbr->delRate,
				mr, bbr->bw_inuse, bbr->pkt_epoch);
			if (cbw)
				free(cbw);
			if (cr)
				free(cr);
			if (mr)
				free(mr);
		} else if (bbr->flex8 == 10) {
			uint32_t new_per, alt, rtt, gp_rtt_mul, minrtt;
			int32_t mrtt_diff;

			new_per = (bbr->bw_inuse >> 32) & 0x00000000ffffffff;
			alt = (bbr->bw_inuse & 0x00000000ffffffff);

			rtt = (bbr->cur_del_rate & 0x00000000ffffffff);
			mrtt_diff = (int32_t) rtt;
			rtt = (bbr->cur_del_rate  >> 32) & 0x00000000ffffffff;
			/* delRate */
			gp_rtt_mul = (bbr->delRate  >> 32) & 0x00000000ffffffff;
			minrtt = (bbr->delRate & 0x00000000ffffffff);
			fprintf(out, "Off times new_per:%u alt:%u rtt:%u rtt_diff:%d gp_rtt_mul:%u minrtt:%u Line:%u\n",
				new_per, alt,
				rtt, mrtt_diff,
				gp_rtt_mul, minrtt, bbr->pkt_epoch);
		} else if (bbr->flex8 == 11) {
			char *gpbw;

			gpbw = display_bw(bbr->rttProp, 0);
			fprintf(out,
				"Timely Lost b/w no-chg ss:%u ca:%u rec:%u [lup:%d ldw:%d ASIR:0x%x] bw:%s(%lu) DRSC:0x%x Line:%u\n",
				bbr->flex4,
				bbr->flex5,
				bbr->flex6,
				bbr->flex3, bbr->flex7, bbr->flex2, gpbw, bbr->rttProp, bbr->cwnd_gain, bbr->pkt_epoch
				);

		} else if (bbr->flex8 == 12) {
			char *gpbw;

			gpbw = display_bw(bbr->rttProp, 0);
			fprintf(out,
				"Timely Gained b/w no-chg ss:%u ca:%u rec:%u [lup:%d ldw:%d ASIR:0x%x] bw:%s(%lu) DRSC:0x%x Line:%u\n",
				bbr->flex4,
				bbr->flex5,
				bbr->flex6,
				bbr->flex3, bbr->flex7, bbr->flex2, gpbw, bbr->rttProp, bbr->cwnd_gain, bbr->pkt_epoch
				);
		} else if (bbr->flex8 == 14) {
			uint32_t minrtt;
			int32_t rttdiff;

			minrtt = (bbr->delRate & 0x00000000ffffffff);
			rttdiff = (int32_t)((bbr->delRate >> 32) & 0x00000000ffffffff);
			fprintf(out,
				"Timely get_decrease decr_per:%u cur_per:%lu minrtt:%u rttdiff:%d  result:%lu line:%u\n",
				bbr->flex1,
				bbr->cur_del_rate,
				minrtt, rttdiff,
				bbr->bw_inuse,
				bbr->pkt_epoch);
		} else if (bbr->flex8 == 15) {
			uint32_t highrtt, rtt;

			highrtt = (bbr->delRate & 0x00000000ffffffff);
			rtt = (uint32_t)((bbr->delRate >> 32) & 0x00000000ffffffff);
			fprintf(out,
				"Timely get_decrease decr_per:%u cur_per:%lu high_rtt:%u rtt:%u result:%lu line:%u\n",
				bbr->flex1,
				bbr->cur_del_rate,
				highrtt, rtt,
				bbr->bw_inuse,
				bbr->pkt_epoch);
		} else {
			fprintf(out, " Unknown Timely log %d Line:%u\n", bbr->flex8, bbr->pkt_epoch);
		}
		break;
	case BBR_LOG_RTO:
		val = bbr->flex8;
		if (val == 0xff) {
			fprintf(out, "User Closes inp:%d state:%d newstate:%d so_error:%d must:%d snd_max_at:%u out_at_rto:%u\n",
				bbr->inhpts,
				bbr->flex1,
				bbr->flex2,
				bbr->flex3,
				bbr->pacing_gain, bbr->delivered, bbr->pkts_out);
		} else {
			if (val > 6)
				val = 0;
			fprintf(out, "Type:%s min_rtt:%u rack_rtt:%u out:%u cw:%u rw:%u t_flags:0x%x out:%d (ip:%d) state:%u prr:%u must:%d snd_max_at:%u out_at_rto:%u\n",
				timer_types[val],
				bbr->flex1,
				bbr->flex2,
				(l->tlb_snd_max - l->tlb_snd_una),
				l->tlb_snd_cwnd,
				l->tlb_snd_wnd, l->tlb_flags,
				(l->tlb_snd_max - l->tlb_snd_una), bbr->inhpts, l->tlb_state, bbr->flex5,
				bbr->pacing_gain, bbr->delivered, bbr->pkts_out);
		}
		break;
	case BBR_LOG_BBRRTT:
	{
		int32_t new_rtt_diff;
		double norm_grad;
		const char *override;
		uint64_t bw, rtt, calc_bw;

		bw = l->tlb_snd_wnd;
		if (bw > l->tlb_snd_cwnd)
			bw =  l->tlb_snd_cwnd;
		calc_bw = bw * 1000000;
		rtt = bbr->flex1;
		if (rtt)
			calc_bw /= rtt;
		else
			calc_bw = 0;
		last_rtt_measure = bbr->flex1;
		if (prtt_set == 0) {
			prtt_set = 1;
			gp_srtt = min_rtt_seen = max_rtt_seen = prev_rtt = bbr->flex1;
			new_rtt_diff = 0;
			norm_grad = 0.0;
		} else {
			if (min_rtt_seen > bbr->flex1)
				min_rtt_seen = bbr->flex1;
			if (max_rtt_seen < bbr->flex1)
				max_rtt_seen = bbr->flex1;
			new_rtt_diff = (int32_t)bbr->flex1 - prev_rtt;
			prev_rtt = (int32_t)bbr->flex1;
			if (rtt_diff_set == 0) {
				rtt_diff = new_rtt_diff;
				rtt_diff_set = 1;
			} else {
				/*
				 * lets take 1/8 of the new diff
				 * and add it to 7/8th the old
				 * to get a EWMA
				 */
				rtt_diff -= (rtt_diff/8);
				rtt_diff += (new_rtt_diff/8);
			}
			norm_grad = (double)rtt_diff / (double)min_rtt_seen;
			/* Update the GP  measurement based srtt */
			gp_srtt -= (gp_srtt / 8);
			gp_srtt += (bbr->flex1 / 8);
		}
		if (bbr->flex1 > (4 * bbr->flex3)) {
			override = "RED";
		} else if (bbr->flex1 == bbr->flex3) {
			override = "INC";
		} else {
			override = "USE GRAD";
		}
		fprintf(out, "rtt:%u len:%u avail:%u flight:%u (ip:%d) state:%u prr:%u NG:%f(%s) conf:%u (max poss bw %s with win:%lu) t_flags:0x%x t_flags2:0x%x\n",
			bbr->flex1,
			bbr->flex2,
			l->tlb_txbuf.tls_sb_acc,
			bbr->inflight,
			bbr->inhpts, l->tlb_state, bbr->pkts_out,
			norm_grad, ((norm_grad <= 0.0) ? "INC" : "DEC"),
			bbr->flex7, display_bw(calc_bw, 0), bw,
			l->tlb_flags, l->tlb_flags2);
		if (extra_print) {
			uint32_t arrv, snd;
			print_out_space(out);
			fprintf(out, " cw:%u sst:%u start:%u end:%u rtt_diff:%d nrtt_diff:%d %s f4:%u f5:%u minrtt:%u rttcnt:%d\n",
				l->tlb_snd_cwnd, l->tlb_snd_ssthresh,
				bbr->pkt_epoch, bbr->lost,
				rtt_diff, new_rtt_diff, override, bbr->flex4,
				bbr->flex5, bbr->flex3, bbr->delivered);
			print_out_space(out);
			fprintf(out,
				"tar:%u prtt_st:%u flags:0x%x (Hibuf,Fora,Gpdy,Inprtt,Measaw,Appl,GPfill,Dragged)\n",
				bbr->applimited,
				bbr->epoch,
				bbr->use_lt_bw);
			print_out_space(out);
			arrv = ((bbr->bw_inuse >> 32) & 0x00000000ffffffff);
			snd = (bbr->bw_inuse & 0x00000000ffffffff);
			fprintf(out,
				"prtt_en:%u (ago:%u) low_rtt_us:%lu gp_srtt:%lu rtr_cnt:%d arr:%u snd:%u rsm_flags:0x%x\n",
				bbr->lt_epoch,
				(bbr->timeStamp - bbr->lt_epoch),
				bbr->cur_del_rate,
				bbr->delRate,
				bbr->cwnd_gain,
				arrv, snd,
				bbr->pacing_gain);
		}
		break;
	}
	default:
	case TCP_LOG_PRR:
	case TCP_LOG_REORDER:
	case TCP_LOG_HPTS:
	case BBR_LOG_EXIT_GAIN:
	case BBR_LOG_PERSIST:
	case BBR_LOG_PKT_EPOCH:
	case BBR_LOG_ACKCLEAR:
	case BBR_LOG_INQUEUE:
	case BBR_LOG_ENTREC:
	case BBR_LOG_EXITREC:
	case BBR_LOG_BWSAMP:
	case BBR_LOG_MSGSIZE:
	case BBR_LOG_STATE:
		fprintf(out, " new msg %d? --- huh\n", id);
		break;
	};
	if (change_tracking)
		change_tracking_check(l);
}

static int force_bbr=0;
static int dump_sn = 0;
static uint32_t first_byte_in = 0;
static uint32_t first_byte_out = 0;
static uint32_t starttime = 0;

static void
dump_default_log_entry(const struct tcp_log_buffer *l, const struct tcphdr *th)
{
	int off_len;
	uint32_t th_ack, th_seq, timeoff, calc;
	char *mask;
	int id;
	const uint8_t *optptr;
	struct timeval wct;
	const struct tcp_log_bbr *bbr;
	struct tcpopt to;

	if (l->tlb_eventid == BBR_LOG_RTT_SHRINKS) {
		dump_log_entry(l, th);
		return;
	}
	bbr = &l->tlb_stackinfo.u_bbr;
	if (lh != NULL) {
		if (tag_dumped == 0) {
			tag_dumped = 1;
			strcpy(log_tag, lh->tlh_tag);
		}
		wct.tv_sec = lh->tlh_offset.tv_sec + l->tlb_tv.tv_sec;
		wct.tv_usec = lh->tlh_offset.tv_usec + l->tlb_tv.tv_usec;
		while (wct.tv_usec > 1000000) {
			wct.tv_usec -= 1000000;
			wct.tv_sec++;
		}
		last_time.tv_sec = wct.tv_sec;
		last_time.tv_usec = wct.tv_usec;
	}
	if ((lh != NULL) && early_filled == 0) {
		uint32_t ticks_passed, sec, usec;

		early_filled = 1;
		earliest_time.tv_sec = wct.tv_sec;
		earliest_time.tv_usec = wct.tv_usec;
		connection_begin_time.tv_sec = earliest_time.tv_sec;
		connection_begin_time.tv_usec = earliest_time.tv_usec;
		/* Now how many ticks since we started have passed? */
		ticks_passed = l->tlb_ticks - l->tlb_starttime;
		/* Back up our earliest time by that many ticks */
		sec = ticks_passed / 1000;
		usec = ticks_passed % 1000;
		usec *= 1000;
		if (usec > earliest_time.tv_usec) {
			connection_begin_time.tv_sec--;
			connection_begin_time.tv_usec += 1000000;
		}
		connection_begin_time.tv_usec -= usec;
		connection_begin_time.tv_sec -= sec;
	}
	id = l->tlb_eventid;
	if (id == TCP_LOG_ACCOUNTING) {
		dump_accounting(l);
		return;
	}
	if (id == TCP_LOG_SOCKET_OPT) sock_opt_cnt++;
	if (prev_tick == 0) {
		prev_tick_set = l->tlb_ticks;
		prev_tick = 1;
	}
	timeoff = l->tlb_ticks - prev_tick;
	prev_tick = l->tlb_ticks;
	fprintf(out, "%u %u def [%u] %s ",  l->tlb_ticks, number_flow, timeoff, evt_name(id));
	switch (id) {
	default:
	case TCP_LOG_PRR:
	case TCP_LOG_REORDER:
	case TCP_LOG_HPTS:
	case BBR_LOG_EXIT_GAIN:
	case BBR_LOG_PERSIST:
	case BBR_LOG_DOSEG_DONE:
	case BBR_LOG_PKT_EPOCH:
	case BBR_LOG_BBRUPD:
	case BBR_LOG_ACKCLEAR:
	case BBR_LOG_INQUEUE:
	case BBR_LOG_TIMERCANC:
	case BBR_LOG_ENTREC:
	case BBR_LOG_EXITREC:
	case BBR_LOG_CWND:
	case BBR_LOG_BWSAMP:
	case BBR_LOG_MSGSIZE:
	case BBR_LOG_BBRSND:
	case BBR_LOG_STATE:
	case BBR_LOG_JUSTRET:
	case BBR_LOG_RTO:
	case BBR_LOG_BBRRTT:
		fprintf(out, " new msg?\n");
		break;
	case TCP_SACK_FILTER_RES:
		dump_sack_filter(bbr);
		break;
	case TCP_LOG_LRO:
		dump_out_lro_log(l, bbr);
		break;
	case BBR_LOG_TIMERSTAR:
		if (show_all_messages) {
			const char *which_one;

			mask = get_timer_mask(bbr->flex3);
			if (bbr->flex8) {
				which_one = "pacer";
			} else {
				which_one =  "timer";
			}
			fprintf(out, "type:%s(%s) srtt:%d for %u(%u) cw:%u rw:%u (ip:%d) rc:%d hpts_slot:%d t_rxtcur:%u frm:%d\n",
				mask,
				which_one,
				bbr->flex1,
				bbr->flex2, bbr->flex4,
				l->tlb_snd_cwnd, l->tlb_snd_wnd,
				bbr->inhpts,
				bbr->flex4, bbr->flex5, bbr->flex6, bbr->flex8);
		}
		break;
	case TCP_LOG_FLOWEND:
		fprintf(out, " iss:%u snd_una:%u snd_max:%u (out:%u) start:%u rcv_nxt:%u avail:%u\n",
			l->tlb_iss,
			l->tlb_snd_una,
			l->tlb_snd_max,
			(l->tlb_snd_max - l->tlb_snd_una),
			l->tlb_starttime,
			l->tlb_rcv_nxt,
			l->tlb_txbuf.tls_sb_acc);
		break;
	case RACK_DSACK_HANDLING:
		printf(" -- Unexpected\n");
		break;
	case TCP_LOG_RTT:
		fprintf(out, " rtt:%u applied to srtt %u var %u\n",
			bbr->flex1,
			((l->tlb_srtt * 1000) >> TCP_RTT_SHIFT), ((l->tlb_rttvar * 1000) >> TCP_RTT_SHIFT));
		break;
	case TCP_LOG_SOCKET_OPT:
		display_tcp_option(l);
		break;
	case  TCP_LOG_USERSEND:
		fprintf(out, "avail:%u pending:%u snd_una:%u snd_max:%u out:%u t_flags:0x%x\n",
			l->tlb_txbuf.tls_sb_acc,
			l->tlb_txbuf.tls_sb_ccc,
			l->tlb_snd_una,
			l->tlb_snd_max,
			(l->tlb_snd_max - l->tlb_snd_una),
			l->tlb_flags);
		break;
	case TCP_LOG_SENDFILE:
		handle_sendfile_log_entry(l);
		break;
	case TCP_LOG_REQ_T:
		tcp_display_http_log(l, bbr);
		break;
	case TCP_HYSTART:
		show_hystart(l, bbr);
		break;
	case TCP_LOG_IN:
	{
		uint32_t snd_una;

		snd_una = l->tlb_snd_una;
		if (th) {
			th_ack = ntohl(th->th_ack);
			th_seq = ntohl(th->th_seq);
			if (irs_set == 0) {
				irs = th_seq;
				irs_set = 1;
			}
			if (use_relative_seq) {
				th_seq -= irs;
				th_ack -= l->tlb_iss;
				snd_una -= l->tlb_iss;
			}
			off_len = th->th_off << 2;
		} else {
			off_len = 0;
			th_ack = 0xbadbad;
			th_seq = 0xbadbad;
		}
		fprintf(out, "Acks %u (%s) off:%u out:%u lenin:%u avail:%u cw:%u rw:%u th_seq:%u una:%u th_ack:%u rto:%u srtt:%u state:%d\n",
			(th_ack - snd_una),
			translate_flags(tcp_get_flags(th)),
			off_len,
			(l->tlb_snd_max - l->tlb_snd_una),
			l->tlb_len,
			l->tlb_txbuf.tls_sb_acc,
			l->tlb_snd_cwnd,
			l->tlb_snd_wnd,
			th_seq,
			snd_una,
			th_ack,
			((((l->tlb_srtt >> 3) + l->tlb_rttvar) >> 2)),
			(l->tlb_srtt >> 5), l->tlb_state
			);
		optptr = (const uint8_t *)th;
		optptr += sizeof(struct tcphdr);
		process_options(&to, th, optptr);
		if (to.to_flags & TOF_SACK) {
			print_sack_blocks(&to, th_ack);
		}
		break;
	}
	case TCP_LOG_REASS:
		print_tcp_log_reass(l, bbr);
		break;
	case TCP_LOG_CONNEND:
		display_connection_end(l, bbr);
		break;
	case TCP_HDWR_PACE_SIZE:
		print_pace_size(l, bbr);
		break;
	case TCP_CHG_QUERY:
		display_change_query(l, bbr);
		break;
	case TCP_RACK_TP_TRIGGERED:
		display_tp_trigger(l);
		break;
	case TCP_HYBRID_PACING_LOG:
		display_hybrid_pacing(l, bbr);
		break;
	case TCP_LOG_PRU:
		display_pru(l);
		break;
	case TCP_LOG_RTO:
		display_tcp_rto(l);
		break;
	case TCP_LOG_OUT:
	{
		char rtr;
		const char *flags_out;
		if (th) {
			th_ack = ntohl(th->th_ack);
			th_seq = ntohl(th->th_seq);
			if (use_relative_seq) {
				th_seq -= l->tlb_iss;
			}
			off_len = th->th_off << 2;
			flags_out = translate_flags(tcp_get_flags(th));
		} else {
			th_ack = 0xbadbad;
			th_seq = 0xbadbad;
			flags_out = "no:th";
			off_len = 0;
		}
		if (seq_set == 0) {
			next_seq = th_seq;
			seq_set = 1;
		}
		if (next_seq == th_seq) {
			rtr = ' ';
		} else {
			if (l->tlb_len)
				rtr = '*';
			else
				rtr = 'A';
		}
		if (l->tlb_errno == -1)
			fprintf(out, "Sent %u:%u%c (%s) th_ack:%u off:%u out:%u avail:%d cw:%u rw:%u ssthresh:%u state:%d rcv_nxt:%u\n",
				th_seq, l->tlb_len, rtr,
				flags_out, th_ack, off_len,
				(l->tlb_snd_max - l->tlb_snd_una),
				l->tlb_txbuf.tls_sb_acc,
				l->tlb_snd_cwnd,
				l->tlb_snd_wnd, l->tlb_snd_ssthresh,
				l->tlb_state, l->tlb_rcv_nxt);
		else
			fprintf(out, "Sent %u:%u%c (%s:%d) th_ack:%u out:%u avail:%d cw:%u rw:%u ssthresh:%u state:%d\n",
				th_seq, l->tlb_len, rtr,
				flags_out, l->tlb_errno, th_ack,
				(l->tlb_snd_max - l->tlb_snd_una),
				l->tlb_txbuf.tls_sb_acc,
				l->tlb_snd_cwnd,
				l->tlb_snd_wnd, l->tlb_snd_ssthresh, l->tlb_state);

		calc = th_seq + l->tlb_len;
		if (SEQ_GT(calc, next_seq))
			next_seq = calc;
		break;
	}
	}
	if (change_tracking)
		change_tracking_check(l);
}

static int force_rack=0;
static int force_default=0;

static uint32_t stack_cnts[10];
static int print_out_time_offset = 0;
static struct tcp_log_buffer aux_buf;
static int summary = 0;

static void
read_pcap_records(const char *filein, int *c)
{
	const struct tcp_log_buffer *lbufp;
	const struct tcphdr *th;
	const char *stackname;
	void *ctx;
	int cnt, warnedstack;
	int need_conversion = 0;

	cnt = 0;
	ctx = bbr_init_file(filein, 1);
	if (ctx == NULL) {
		printf("Failed to init context with file %s\n",
		       filein);
		return;
	}
	lh = bbr_get_tlh(ctx);
	/* Will we need a conversion? */
	if (lh->tlh_version != TCP_LOG_BUF_VER)
		need_conversion = 1;
	th = NULL;
	if (display_file_names) {
		fprintf(out, "## FILE %s\n", filein);
	}
	warnedstack = -1;
	if (print_out_time_offset) {
		if (lh) {
			fprintf(out, "## Time offset %lu.%lu\n",
				lh->tlh_offset.tv_sec,
				lh->tlh_offset.tv_usec);
		}
	}
	while(bbr_get_next(ctx, &lbufp, &th) == 0) {
		if (need_conversion) {
			if (bbr_convert(ctx, lbufp, &aux_buf) != 0) {
				fprintf(stderr,
					"Fatal error log version was %d and conversion to type %d failed\n",
					lh->tlh_version, TCP_LOG_BUF_VER);
				exit(-1);
			}
			lbufp = &aux_buf;
		}
		if (lbufp->tlb_stackid >= 10) {
			stack_cnts[9]++;
		} else {
			stack_cnts[lbufp->tlb_stackid]++;
		}
		msg_types_list[lbufp->tlb_eventid]++;
		if (summary)
			continue;
		if (lbufp->tlb_starttime && (starttime != lbufp->tlb_starttime)) {
			starttime = lbufp->tlb_starttime;
		}
		if (lbufp->tlb_fbyte_in && (first_byte_in != lbufp->tlb_fbyte_in)) {
			first_byte_in = lbufp->tlb_fbyte_in;
		}
		if (lbufp->tlb_fbyte_out && (first_byte_out != lbufp->tlb_fbyte_out)) {
			first_byte_out = lbufp->tlb_fbyte_out;
		}
		if (num_start_set) {
			if (SEQ_LT(lbufp->tlb_sn, record_num_start))
				continue;
		}
		if (num_end_set) {
			if (SEQ_GT(lbufp->tlb_sn, record_num_end))
				continue;
		}
		stackname = bbr_get_stackname(ctx, lbufp->tlb_stackid);
		if (dump_sn) {
			fprintf(out, "%s:%d:sn:%u type:%u:",
				stackname,
				lbufp->tlb_stackid,
				lbufp->tlb_sn,
				lbufp->tlb_eventid);
		}
		if (force_bbr || !strncmp(stackname, "bbr", 3)) {
			if (print_out_time_offset) {
				fprintf(out, "%lu.%lu:",
					lbufp->tlb_tv.tv_sec,
					lbufp->tlb_tv.tv_usec);
			}
			dump_log_entry(lbufp, th);
		} else if (force_rack || !strncmp(stackname, "rack", 4)) {
			dump_rack_log_entry(lbufp, th);
		} else if (force_default) {
			dump_default_log_entry(lbufp, th);
		} else {
			/* Treat everything else as default. */
			int def_or_freebsd = 0;
			if (strncmp(stackname, "default", 7) == 0)
				def_or_freebsd = 1;
			if (strncmp(stackname, "freebsd", 7) == 0)
				def_or_freebsd = 1;
			if ((def_or_freebsd == 0) &&
			    warnedstack != lbufp->tlb_stackid) {
				fprintf(stderr, "WARNING: Treating stack "
				    "%s (%hhu) as the default stack\n",
				    stackname, lbufp->tlb_stackid);
				warnedstack = lbufp->tlb_stackid;
			}
			dump_default_log_entry(lbufp, th);
		}
		th = NULL;
		cnt++;
	}
	*c += cnt;
	bbr_fini(ctx);
}

static void
deconstruct_filename(char *filename, int *file_no, int full_filename, int has_xz)
{
	char sbuf_name[1024];
	int len, i, set_dirname = 0;
	int dot_count, dot_req;
	char *num;
	struct stat sbuf;

	if (full_filename == 0) {
		goto path_construction;
	}
retry_wdir:
	if (dirname == NULL)
		strcpy(sbuf_name, filename);
	else
		sprintf(sbuf_name, "%s/%s", dirname, filename);
	if (stat(sbuf_name, &sbuf) != 0) {
		if (dirname == NULL) {
			set_dirname = 1;
			dirname = "/var/log/tcplog_dumps";
			goto retry_wdir;
		}
		if (set_dirname) {
			dirname = NULL;
			set_dirname = 0;
		}
		fprintf(stderr, "Can't find file %s\n", filename);
		exit(-1);
	}
	dot_count = 0;
	if (has_xz)
		dot_req = 3;
	else
		dot_req = 2;
	len  = strlen(filename);
	for(i=(len-1); len > 7 ; i--) {
		if (filename[i] == '.') {
			dot_count++;
			if (dot_count == dot_req) {
				filename[i] = 0;
				num = &filename[(i+1)];
				*file_no = strtol(num, NULL, 0);
				return;
			}
		}
	}
	fprintf(stderr, "Can't find required num of dots (%d) found:%d in filename:%s\n",
		dot_req, dot_count, filename);
	exit(-1);
path_construction:
	/*
	 * Here we don't have a full file name
	 * instead we have blahblahblah
	 * not blahblahblah.N.pcapng or
	 * blahblahblah.N.pcapng.xz
	 * lets look for that.
	 */
	has_xz = 0;
	set_dirname = 0;
retry_from_dir:
	if (dirname == NULL)
		sprintf(sbuf_name, "%s.%d.pcapng",
			filename, *file_no);
	else
		sprintf(sbuf_name, "%s/%s.%d.pcapng",
			dirname,
			filename, *file_no);
retry_stat:
	if (stat(sbuf_name, &sbuf) != 0) {
		if (has_xz == 0) {
			has_xz = 1;
			if (dirname == NULL)
				sprintf(sbuf_name, "%s.%d.pcapng.xz",
					filename, *file_no);
			else
				sprintf(sbuf_name, "%s/%s.%d.pcapng.xz",
					dirname,
					filename, *file_no);
			goto retry_stat;
		}
		if (dirname == NULL) {
			/* Ok lets reset and try with default dir */
			has_xz = 0;
			set_dirname = 1;
			dirname = "/var/log/tcplog_dumps";
			goto retry_from_dir;
		}
		if (set_dirname) {
			dirname = NULL;
			set_dirname = 0;
		}
		fprintf(stderr, "Cannot find %s.%d.pcapng[.xz]\n",
			filename, *file_no);
		exit(-1);
	}
	/*
	 * ok the path is valid with the dirname nothing left to
	 * do to de-construct it.
	 */
	return;
}

static void
parse_out_file_info(char *filename, const char *i_filename, int *file_no)
{
	int len;
	int is_xz = 0;

	strcpy(filename, i_filename);
	len = strlen(filename);
	if (len < 9) {
		deconstruct_filename(filename, file_no, 0, is_xz);
		return;
	}
	if (strcmp(&filename[(len-3)], ".xz") == 0) {
		/* We have a full file with .xz on the end */
		is_xz = 1;
	}
	if (is_xz == 0) {
		if (strcmp(&filename[(len-7)], ".pcapng") != 0) {
			deconstruct_filename(filename, file_no, 0, is_xz);
			return;
		}
	}
	deconstruct_filename(filename, file_no, 1, is_xz);
	return;
}

int
main(int argc, char **argv)
{
	const char *i_filename=NULL;
	char filename[1024];
	char file_construct[1024];
	double top, bot, perc;
	struct stat sbuf;
	int i, cnt=0;
	int notdone=1;
	int file_no=0;
	int file_no_start;
	uint64_t actual_sending_time=0;
	uint64_t tot=0;
	int show_msg_stats=0;

	memset(time_in_state, 0, sizeof(time_in_state));
	memset(msg_types_list, 0, sizeof(msg_types_list));
	memset(sent_state, 0, sizeof(sent_state));
	memset(time_in_major_states, 0, sizeof(time_in_major_states));
	memset(time_in_sub_states, 0, sizeof(time_in_sub_states));
	out = stdout;
	memset(stack_cnts, 0, sizeof(stack_cnts));
	while ((i = getopt(argc, argv, "6A:b:cCd:D:ef:Fi:klL:mMN:o:OprRsS:tTUvw:WxYzZ:?")) != -1) {
		switch (i) {
		case '6':
			v6 = 1;
			break;
		case 'A':
			record_num_start = strtoul(optarg, NULL, 0);
			num_start_set = 1;
			break;
		case 'b':
			first_time = strtoul(optarg, NULL, 0);
			first_time_set = 1;
			break;
		case 'c':
			use_relative_seq = 1;
			break;
		case 'C':
			lro_flush_is_ms = 1;
			break;
		case 'd':
			dirname = optarg;
			break;
		case 'D':
			dump_out_sack = fopen(optarg, "w");
			if (dump_out_sack == NULL) {
				fprintf(stderr, "No sack information will be dumped can't open %s\n",
					optarg);
			}
		case 'e':
			extra_print = 1;
			break;
		case 'f':
			if (strcmp(optarg, "bbr") == 0)
				force_bbr = 1;
			else if (strcmp(optarg, "rack") == 0)
				force_rack = 1;
			else if (strcmp(optarg, "default") == 0)
				force_default = 1;
			else
				fprintf(stderr, "Unknown stack %s can't force that mode\n", optarg);
			break;
		case 'F':
			display_file_names = 1;
			break;
	        case 'i':
			i_filename = optarg;
			break;
		case 'k':
			add_colon = 1;
			break;
		case 'l':
			log_all_state_change = 0;
			break;
		case 'L':
			file_count_limit = strtol(optarg, NULL, 0);
			break;
		case 'm':
			show_msg_stats = 1;
			break;
		case 'M':
			use_monolithic_time = 1;
			break;
		case 'N':
			number_flow = strtol(optarg, NULL, 0);
			break;
		case 'o':
			out = fopen(optarg, "w");
			if (out == NULL) {
				fprintf(stderr, "Can't open %s for output err:%d\n",
					optarg, errno);
				exit(-1);
			}
			break;
		case 'O':
			show_all_messages = 0;
			break;
		case 'p':
			print_out_time_offset = 1;
			break;
 		case 'r':
			time_is_relative = 1;
			break;
		case 'R':
			show_record = 1;
			break;
		case 's':
			show_msg_stats = 1;
			summary = 1;
			break;
		case 'S':
			file_no = strtol(optarg, NULL, 0);
			break;
		case 't':
			print_out_the_time = 1;
			break;
		case 'T':
			use_timestamp = 0;
			break;
		case 'U':
			include_user_send = 1;
			break;
		case 'v':
			change_tracking = 1;
			break;
		case 'w':
			warn_behind = strtoul(optarg, NULL, 0);;
			break;
		case 'W':
			display_wallclock_time = 1;
			break;
		case 'x':
			showExtraInfo = 1;
			break;
		case 'Y':
			dump_sn = 1;
			break;
		case 'z':
			/* Toggle the sort sack flag */
			if (sort_all_sacks)
				sort_all_sacks = 0;
			else if (sort_all_sacks == 0)
				sort_all_sacks = 1;
			break;
		case 'Z':
			record_num_end = strtoul(optarg, NULL, 0);
			num_end_set = 1;
			break;
		case '?':
		default:
		use:
			fprintf(stderr, "%s -i sessionid  [-d dir -S no -F -l -O -N -n -r -t -U -D sack-dump-file -e -w cnt -s statck]\n",
				argv[0]);
			fprintf(stderr, " -A recsn -- Do not display record serial numbers less than recsn\n");
			fprintf(stderr, " -b time - Consider the first time mark to be this usec value (use for relative to some other file)\n");
			fprintf(stderr, " -c relative sequence numbers\n");
			fprintf(stderr, " -d directory-where-files-are (default=/var/log/tcplog_dumps)\n");
			fprintf(stderr, " -D file - specify a file to dump sack logging information to\n");
			fprintf(stderr, " -e - enable extra printing\n");
			fprintf(stderr, " -f stackname - Force interpret to this stack name\n");
			fprintf(stderr, " -F add file name in output\n");
			fprintf(stderr, " -i sessionid - display the specified session\n");
			fprintf(stderr, " -l don't log all state transistions don't collapse the probe_bw neutral ones\n");
			fprintf(stderr, " -k add a : to the rack time print\n");
			fprintf(stderr, " -L cnt - Set a maximum of cnt limit to the number of .xz files to read\n");
			fprintf(stderr, " -m - show message stats summary at the end\n");
			fprintf(stderr, " -N num - place flow-num after the time (def=0)\n");
			fprintf(stderr, " -o output - direct output to this file not stdout\n");
			fprintf(stderr, " -O condense message output showing minimal information\n");
			fprintf(stderr, " -r relative time on\n");
			fprintf(stderr, " -R - Show record numbers at the edge of the trace\n");
			fprintf(stderr, " -s stack - surpress the printing of all but the message summary\n");
			fprintf(stderr, " -S num - Don't start at file number 0, start at num\n");
			fprintf(stderr, " -t print out the time too\n");
			fprintf(stderr, " -T -- For rack don't use the bbr->timestamp field (usecs) and use ticks\n");
			fprintf(stderr, " -s -- Instead of displaying the log, display only the message summary\n");
			fprintf(stderr, " -U include user send events in the display\n");
			fprintf(stderr, " -v turn on change tracking to observe changes in the base BB entries\n");
			fprintf(stderr, " -w behindcnt -- Warn to stderr if we get behind over behindcnt\n");
			fprintf(stderr, " -W -- Display wallclock time\n");
			fprintf(stderr, " -Y -- Announce the full stack name\n");
			fprintf(stderr, " -z -- toggle the sort-sack flag (on by default)\n");
			fprintf(stderr, " -Z recsn -- Do not display record serial numbers over recsn\n");
			fprintf(stderr, " -? - get this help message and exit\n");
			exit(-1);
			break;
		};
	}
	if (i_filename == NULL)
		goto use;

	memset(filename, 0, sizeof(filename));
	parse_out_file_info(filename, i_filename, &file_no);
	file_no_start = file_no;
	while (notdone) {
		if (dirname) {
			sprintf(file_construct, "%s/%s.%d.pcapng.xz",
				dirname, filename, file_no);

		} else {
			sprintf(file_construct, "%s.%d.pcapng.xz",
				filename, file_no);
		}
		if (stat(file_construct, &sbuf)) {
			if (dirname) {
				sprintf(file_construct, "%s/%s.%d.pcapng", dirname, filename, file_no);
			} else {
				sprintf(file_construct, "%s.%d.pcapng", filename, file_no);
			}
			if (stat(file_construct, &sbuf) == -1) {
				notdone = 0;
				if (file_no == 0) {
					printf("Could not find file %s (or .xz version)\n", file_construct);
					exit(-1);
				}
				continue;
			}
		}
		read_pcap_records(file_construct, &cnt);
		file_no++;
		file_count_at++;
		if (file_count_limit && (file_count_at >= file_count_limit))
			break;
	}
	fprintf(stderr,
		"Files:%d Processed %d records\n",
		(file_no - file_no_start),
		cnt);
	for(i=0; i<10; i++) {
		if (stack_cnts[i]) {
			fprintf(stderr, "Saw %d records from stackid:%d total_missed:%ld dups:%u\n",
				stack_cnts[i], i, total_missed_records, duplicates);
		}
	}
	if (summary) {
		goto do_msg_summary;
	}
	if (show_all_messages == 0) {
		fprintf(out, "# ");
	}
	if (is_bbr) {
		/* First do final accounting for states */
		if (state_is_set) {
			if (TSTMP_GT(last_time_stamp, state_transition_time)) {
				time_in_major_states[(major_stateval-1)] += (last_time_stamp - state_transition_time);
			}
			if ((major_stateval == BBR_STATE_PROBE_BW) && minor_is_set) {
				if (TSTMP_GT(last_time_stamp, minor_state_transition_time)) {
					time_in_sub_states[minor_state] += (last_time_stamp - minor_state_transition_time);
				}
			}
			state_transition_time = last_time_stamp;
			minor_state_transition_time = last_time_stamp;
		}
		for(i=0; i<9; i++) {
			tot += sent_state[i];
		}
		bot = tot * 1.0;
		for(i=0; i<9; i++) {
			if (tot) {
				top = (sent_state[i] * 100.0);
				perc = top / bot;
			} else {
				perc = 0.0;
			}
			if (show_all_messages == 0) {
				fprintf(out, "# ");
			}
			fprintf(out, "Sent in state:%d %lu [%2.3f%%]\n",
				i, sent_state[i], perc);
		}
		/* Now what about time in states? */
		fprintf(out, "Time in major states\n");
		tot = 0;
		for(i=0; i<5; i++) {
			tot += time_in_major_states[i];
		}
		bot = tot * 1.0;
		for(i=0; i<5; i++) {
			top = time_in_major_states[i] * 1.0;
			perc = (top * 100.0)/bot;
			fprintf(out, "%s time:%lu [%2.3f%%]\n",
				major_state[(i+1)],
				time_in_major_states[i],
				perc);
		}
		tot = 0;
		for(i=0; i<9; i++) {
			tot += time_in_sub_states[i];
		}
		fprintf(out, "Time in PROBE-BW minor states\n");
		bot = tot * 1.0;
		if (tot != time_in_major_states[(BBR_STATE_PROBE_BW-1)]) {
			fprintf(stderr, "***Total is %lu in substate but major had %lu\n",
				tot, time_in_major_states[(BBR_STATE_PROBE_BW-1)]);
		}
		for(i=0; i<9; i++) {
			top = time_in_sub_states[i] * 100.0;
			perc = top / bot;
			if (i < 8)
				fprintf(out, "State:%d time:%lu [%2.3f%%]\n",
					i, time_in_sub_states[i], perc);
			else
				fprintf(out, "State PROBE_BW:Policed time:%lu [%2.3f%%]\n",
					time_in_sub_states[i], perc);
		}
	}
	if (extra_print) {
		if ((lowest_delta != 0xffffffff) &&
		    (highest_delta != 0)) {
			fprintf(out, "Lowest timestamp delta %u, highest %u\n",
				lowest_delta,
				highest_delta);
		}
		fprintf(out, "Wall clock time of trace %lu useconds\n", total_time_in_trace);
		if (total_time_in_trace && total_time_using_lt_bw) {
			bot = total_time_in_trace * 1.0;
			top = total_time_using_lt_bw * 100.0;
			perc = top / bot;
		} else {
			perc = 0.0;
		}
		actual_sending_time = total_time_in_trace - (total_time_no_rwnd + total_time_no_avail);
		if (show_all_messages == 0) {
			fprintf(out, "# ");
		}
		fprintf(out, "Actual amount of time when flow could send %lu useconds\n", actual_sending_time);
		/* Persisting time */
		if (total_time_in_trace && total_time_persisting) {
			bot = total_time_in_trace * 1.0;
			top = total_time_persisting * 100.0;
			perc = top / bot;
		} else {
			perc = 0.0;
		}
		if (show_all_messages == 0) {
			fprintf(out, "# ");
		}
		fprintf(out, "Total time that we were in persists mode %lu [%2.3f%%]\n",
			total_time_persisting,  perc);
		/* no rwnd time, should be same but might not be with data loss */
		if (total_time_persisting != total_time_no_rwnd) {
			if (total_time_in_trace && total_time_no_rwnd) {
				top = total_time_no_rwnd * 100.0;
				bot = total_time_in_trace * 1.0;
				perc = top / bot;

			} else {
				perc = 0.0;
			}
			if (show_all_messages == 0) {
				fprintf(out, "# ");
			}
			fprintf(out, "Total time none rwnd %lu [%2.3f%%]\n",
				total_time_no_rwnd, perc);
		}

		if (total_time_in_trace && total_time_no_avail) {
			top = total_time_no_avail * 100.0;
			bot = total_time_in_trace * 1.0;
			perc = top / bot;

		} else {
			perc = 0.0;
		}
		if (show_all_messages == 0) {
			fprintf(out, "# ");
		}
		fprintf(out, "Total time none avail %lu [%2.3f%%]\n",
			total_time_no_avail, perc);
		if (total_time_in_trace && total_time_app_limited) {
			bot = total_time_in_trace * 1.0;
			top = total_time_app_limited * 100.0;
			perc = top / bot;
		} else {
			perc = 0.0;
		}
		if (show_all_messages == 0) {
			fprintf(out, "# ");
		}
		fprintf(out, "Total time app limited %lu [%2.3f%%] transistions:%lu\n", total_time_app_limited, perc, app_limited_transitions);
		if (total_time_in_trace && total_time_app_limited) {
			bot = total_time_in_trace * 1.0;
			top = total_time_using_lt_bw * 100.0;
			perc = top / bot;
		} else {
			perc = 0.0;
		}
		if (show_all_messages == 0) {
			fprintf(out, "# ");
		}
		fprintf(out, "Total time being policed vs time of trace %lu [%2.3f%%]\n", total_time_using_lt_bw, perc);
		if (actual_sending_time && total_time_ltbw_sendok) {
			bot = actual_sending_time * 1.0;
			top = total_time_ltbw_sendok * 100.0;
			perc = top / bot;
		} else {
			perc = 0.0;
		}
		if (show_all_messages == 0) {
			fprintf(out, "# ");
		}
		fprintf(out, "Total time policed-sending vs sending time of trace %lu [%2.3f%%]\n", total_time_ltbw_sendok, perc);
		if (retran_count && tot) {
			top = retran_count * 100.0;
			perc = top / bot;
			if (show_all_messages == 0) {
				fprintf(out, "# ");
			}
			fprintf(out, "Saw %lu retransmissions loss rate about %2.3f%%\n",
				retran_count, perc);
		}
		fprintf(out, "Flow was hot in lesser for %u useconds\n", time_in_hot);
		fprintf(out, "Saw %lu socket options id's\n", sock_opt_cnt);
		fprintf(out, "SS:%.6f CA:%.6f REC:%.6f\n",
			((time_in_state[0] * 1.0) / 1000000.0),
			((time_in_state[1] * 1.0) / 1000000.0),
			((time_in_state[2] * 1.0) / 1000000.0));

		if (is_bbr) {
			double secs;
			double per;

			bot = (over_256 + at_256 + under_256) * 1.0;
			fprintf(out, "Time stats:\n");
			per = (over_256  * 100.0)/bot;
			secs = (over_256  * 1.0)/1000000.0;
			fprintf(out, "Over  %2.3f [%2.3f%%]\n",
				secs, per);
			per = (at_256  * 100.0)/bot;
			secs = (at_256 * 1.0)/1000000.0;
			fprintf(out, "At    %2.3f [%2.3f%%]\n",
				secs, per);
			per = (under_256  * 100.0)/bot;
			secs = (under_256 * 1.0)/1000000.0;
			fprintf(out, "Under %2.3f [%2.3f%%]\n",
				secs, per);
			fprintf(out, "----------------drain breakdown\n");
			bot = (under_drain + under_rtt + under_subdr) * 1.0;
			per = (under_subdr * 100.0) / bot;
			secs = (under_subdr * 1.0)/1000000.0;
			fprintf(out, "--- BW-Drain    %2.3f [%2.3f%%]\n",
				secs, per);
			per = (under_rtt * 100.0) / bot;
			secs = (under_rtt * 1.0)/1000000.0;
			fprintf(out, "--- ProbeRTT %2.3f [%2.3f%%]\n",
				secs, per);
			per = (under_drain * 100.0) / bot;
			secs = (under_drain * 1.0)/1000000.0;
			fprintf(out, "--- Drain %2.3f [%2.3f%%]\n",
				secs, per);

		}
	}
	if (tag_dumped) {
		fprintf(out, "Tag:%s\n", log_tag);
	}
	if (early_filled) {
		struct tm *tmval;
		char arry[1000];

		memset(arry, 0, sizeof(arry));
		get_end_code_string(endcode, arry);
		tmval = gmtime(&earliest_time.tv_sec);
		fprintf(out, "start:%2.2d/%2.2d/%4.4d %2.2u:%2.2u:%2.2u.%6.6u UTC <-> end:",
			(tmval->tm_mon + 1),
			tmval->tm_mday,
			(tmval->tm_year + 1900),
			tmval->tm_hour,
			tmval->tm_min,
			tmval->tm_sec,
			(int)earliest_time.tv_usec);
		tmval = gmtime(&last_time.tv_sec);
		fprintf(out, "%2.2d/%2.2d/%4.4d %2.2u:%2.2u:%2.2u.%6.6u UTC endcode:0x%lx(%s) txfr:%u\n",
			(tmval->tm_mon + 1),
			tmval->tm_mday,
			(tmval->tm_year + 1900),
			tmval->tm_hour,
			tmval->tm_min,
			tmval->tm_sec,
			(int)last_time.tv_usec, endcode, arry,
			(last_snd_una - first_seq));
		tmval = gmtime(&connection_begin_time.tv_sec);
		fprintf(out, "The connection started at %2.2d/%2.2d/%4.4d %2.2u:%2.2u:%2.2u.%6.6u UTC\n",
			(tmval->tm_mon + 1),
			tmval->tm_mday,
			(tmval->tm_year + 1900),
			tmval->tm_hour,
			tmval->tm_min,
			tmval->tm_sec,
			(int)connection_begin_time.tv_usec);
		if (first_byte_in) {
			fprintf(out,
				"Setup to first byte in %u\n",
				(first_byte_in - starttime));
		}
		if (first_byte_out) {
			fprintf(out,
				"Setup to first byte out %u\n",
				(first_byte_out - starttime));
		}
		if (first_byte_out && first_byte_in) {
			if (first_byte_out > first_byte_in) {
				fprintf(out, "We responded in %d ms to the first request\n",
					(first_byte_out - first_byte_in));
			} else {
				fprintf(out, "The server responded to our request in %d ms\n",
					(first_byte_in - first_byte_out));
			}
		}
	}
	if (dump_out_sack) {
		fprintf(dump_out_sack, "QUIT\n");
		fclose(dump_out_sack);
	}
	fprintf(out, "Total RACK IN:%lu OUT:%lu\n", total_log_in, total_log_out);
do_msg_summary:
	if (show_msg_stats) {
		int len_out,xxx;

		fprintf(out, "*************************************\n");
		fprintf(out, "         MESSAGE SUMMARY\n");
		fprintf(out, "*************************************\n");
		for(i=0; i<MAX_TYPES; i++) {
			if (msg_types_list[i]) {
				len_out = 0;
				len_out = fprintf(out, "%s(%d)",
						 log_names[i], i);
				if (len_out < 25) {
					for(xxx=len_out; xxx < 25; xxx++)
						fprintf(out, " ");
				}
				fprintf(out, "%lu\n", msg_types_list[i]);

			}
		}
	}
	if (out != stdout)
		fclose(out);
	return(0);
}
