#include <sys/types.h>
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
#include <sys/tim_filter.h>
#include <getopt.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#define	_WANT_TCPCB
#include <netinet/tcp_var.h>
#include <arpa/inet.h>
#include <netinet/in_pcb.h>
#include <dev/tcp_log/tcp_log_dev.h>
#include <netinet/tcp_log_buf.h>
#include <netinet/tcp_stacks/sack_filter.h>
#include <netinet/tcp_stacks/tcp_bbr.h>
#include <netinet/tcp_stacks/rack_bbr_common.h>
#include <net/route.h>
#include <netinet/tcp_seq.h>
#include <netinet/tcp_var.h>
#include <netinet/tcp_hpts.h>

#include <assert.h>

#include <bbparse.h>
static uint32_t lowest_delta = 0xffffffff;
static uint32_t highest_delta = 0;
static int32_t showExtraInfo = 0;
static int32_t file_count_limit = 0;
static int32_t file_count_at = 0;

static FILE *dump_out_sack=NULL;
#define	MAX_TYPES  TCP_LOG_END
static int extra_print = 0;
static int number_flow = 0;
static const char *surpress=NULL;
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

/*#define BBR_RED_BW_CONGSIG  	 0	 We enter recovery and set using b/w */
/*#define BBR_RED_BW_RATECAL  	 1	 We are calculating the loss rate */
/*#define BBR_RED_BW_USELRBW       2	 We are dropping the lower b/w with cDR*/
/*#define BBR_RED_BW_SETHIGHLOSS   3	 We have set our highloss value at exit from probe-rtt */
/*#define BBR_RED_BW_PE_CLREARLY    4	 We have decided to clear the reduction early */
/*#define BBR_RED_BW_PE_CLAFDEL	 5	 We are clearing it on schedule delayed */
/*#define BBR_RED_BW_REC_ENDCLL	 6	 Recover exits save high if needed an clear to start measuring */
/*#define BBR_RED_BW_PE_NOEARLY_OUT 7	 Set pkt epoch judged that we do not get out of jail early */

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

static struct timeval earliest_time;
static struct timeval connection_begin_time;
static struct timeval last_time;
static int early_filled = 0;

static uint32_t msg_types_list[MAX_TYPES];
static uint16_t last_major_state = 0;
static uint16_t last_minor_state = 0;
static uint64_t total_missed_records = 0;
static const char *log_names[MAX_TYPES] = {
	"UNKNOWN           ",
	"IN        ", /* Incoming packet                 1 */
	"PKT_OUT   ", /* Transmit (without other event)  2 */
	"RTO       ", /* Retransmit timeout              3 */
	"SOWAKE    ", /* We wokeup a socket buffer       4 */
	"BAD_RETRAN", /* Detected bad retransmission 5 */
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
	"EXTRA_GAIN", /* Extra cwnd gain added            30 */
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
	"BBR_SRTT_GAIN_EVENT",	/* 49 */
	"TCP_LOG_REASS", 	/* 50 */
 	"TCP_HDWR_TLS",		/* 51 */
	"BBR_TCP_HDWR_PACE",	/* 52 */
	"BBR_LOG_TSTMP_VAL",	/* 53 */
	"TCP_LOG_CONNEND", 	/* 54 */
	"TCP_LRO_LOG",		/* 55 */
	"SACK_FILTER_RESULT",	/* 56 */
	"TCP_SAD_DETECTION",	/* 57 */
	"TCP_TIMELY_WORK",	/* 58 */
	"USER_LOG  ",		/* 59 */
	"SENDFILE  ",		/* 60 */
	"TCP_LOG_HTTP_T",	/* 61 */
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
translate_flags(uint8_t flags)
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
	uint32_t va;

	usec_per_sec = 1000000;
	bdp = (rtt * bw)/usec_per_sec;
	va = (uint32_t)bdp;
	return (bdp);
}

static uint32_t
bbr_get_target_cwnd(uint64_t bw, uint64_t rtt, uint32_t gain)
{
	uint64_t bdp, step;
	uint32_t cwnd;
#ifdef DO_ROUND
	uint32_t mss, even_targ;
#endif
	/* Get the bdp from the two values */
	bdp = bbr_get_bw_delay_prod(rtt, bw);

	/* Now apply the gain */
	cwnd = (uint32_t) (((bdp * ((uint64_t) gain)) + (uint64_t) (BBR_UNIT - 1)) / ((uint64_t) BBR_UNIT));
	/* round up to then next mss boundary  */
	step = (bdp * ((uint64_t) gain)) + (uint64_t)(BBR_UNIT - 1);
	step /= (uint64_t)BBR_UNIT;
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

static void inline
print_out_space(FILE *outp)
{
	fprintf(outp, "                             ");
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
dump_sad_values(const struct tcp_log_bbr *bbr)
{
	if (bbr->flex8 == 1) {
		fprintf(out, "Detecting ");
	} else if (bbr->flex8 == 2) {
		fprintf(out, "An Attacker ");
	} else if (bbr->flex8 == 3) {
		fprintf(out, "False Positive ");
	} else {
		fprintf(out, "meth:%d? ", bbr->flex8);
	}
	fprintf(out, "Sacks:%u Acks:%u mv:%u nomv:%u mapa:%u sd:%d\n",
		bbr->flex1, bbr->flex2,
		bbr->flex3, bbr->flex4,
		bbr->flex5, bbr->flex7);
	print_out_space(out);
	fprintf(out, "flight:%u s2ath:%u s2mth:%u fd:%d dd:%d map_lim:%u decay_th:%u\n",
		bbr->inflight,
		bbr->flex6,
		bbr->pkts_out,
		((bbr->lt_epoch >> 8) & 0xff),
		(bbr->lt_epoch & 0xff),
		bbr->applimited, bbr->delivered);
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
#ifdef NETFLIX_TCP_STACK
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
	} else if (opt == TCP_HPTSI) {
		return ("TCP_HPTSI");
	} else if (opt == TCP_MAXUNACKTIME) {
		return ("TCP_MAXUNACKTIME");
	} else if (opt == TCP_MAXPEAKRATE) {
		return ("TCP_MAXPEAKRATE");
	} else if (opt == TCP_IDLE_REDUCE) {
		return ("TCP_IDLE_REDUCE");
	} else if (opt == TCP_REMOTE_UDP_ENCAPS_PORT) {
		return ("TCP_REMOTE_UDP_ENCAPS_PORT");
#endif
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
	} else {
		return ("Unkown?");
	}

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

#ifdef NETFLIX_TCP_STACK
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
		fprintf(out, "Read wakeup recv'd %d bytes -- sbflags 0x%x -- %s avail:%u\n",
			bbr->flex2,  bbr->flex1, ((notify) ? "will wake" : "will not wake"),
			l->tlb_rxbuf.tls_sb_acc);
	} else {
		fprintf(out, "Write wakeup ack'd %u bytes -- sbflags 0x%x -- %s avail:%u\n",
			bbr->flex2,  bbr->flex1, ((notify) ? "will wake" : "will not wake"),
			l->tlb_txbuf.tls_sb_acc);
	}
}
#endif

static void
tcp_display_http_log(const struct tcp_log_buffer *l, const struct tcp_log_bbr * bbr)
{
	char buf[128];
	const char *reas;
#ifdef NETFLIX_TCP_STACK
	if (bbr->flex8 == TCP_HTTP_REQ_LOG_NEW)
		reas = "New entry";
	else if (bbr->flex8 == TCP_HTTP_REQ_LOG_COMPLETE)
		reas = "Complete";
	else if (bbr->flex8 == TCP_HTTP_REQ_LOG_FREED)
		reas = "Freed";
	else if (bbr->flex8 == TCP_HTTP_REQ_LOG_ALLOCFAIL)
		reas = "Alloc Failure";
	else if (bbr->flex8 == TCP_HTTP_REQ_LOG_MOREYET)
		reas = "More to come";
	else if (bbr->flex8 == TCP_HTTP_REQ_LOG_FORCEFREE)
		reas = "Force Free";
	else if (bbr->flex8 == TCP_HTTP_REQ_LOG_STALE)
		reas = "Stale";
	else {
#endif
		sprintf(buf, "Unknown:%d", bbr->flex8);
		reas = buf;
#ifdef NETFLIX_TCP_STACK
	}
#endif
	fprintf(out, " %s COcR:0x%x tm:%lu flg:0x%x [ %lu - ",
		reas,
		bbr->applimited,
		bbr->rttProp,
		bbr->flex3,
		bbr->delRate);
#ifdef NETFLIX_TCP_STACK
	if (bbr->flex3 & TCP_HTTP_TRACK_FLG_OPEN)  {
		fprintf(out, " ] slot:%d\n",
			bbr->flex7);
	} else {
#endif
		fprintf(out, " %lu (%lu) ] slot:%d\n",
			bbr->cur_del_rate,
			(bbr->cur_del_rate - bbr->delRate),
			bbr->flex7);
#ifdef NETFLIX_TCP_STACK
	}
#endif
	if (extra_print) {
		uint64_t nbytes, ltime;
		uint32_t seq_off;

		nbytes = bbr->flex6;
		nbytes <<= 32;
		nbytes |= bbr->epoch;
		ltime = bbr->flex4;
		ltime <<= 32;
		ltime |= bbr->flex5;
		print_out_space(out);
#ifdef NETFLIX_TCP_STACK
		if (bbr->flex3 & TCP_HTTP_TRACK_FLG_OPEN)  {
			if (SEQ_GT(l->tlb_snd_una, bbr->flex1))
				seq_off = l->tlb_snd_una;
			else
				seq_off = bbr->flex1;
		} else
#endif
			seq_off = bbr->flex2;
		fprintf(out, "offset:%lu nbytes:%lu localtime:%lu [tcp sseq:%u eseq:%u (%u) sndmax:%u snduna:%u]\n",
			bbr->bw_inuse, nbytes, ltime,
			bbr->flex1, bbr->flex2, (seq_off - bbr->flex1),
			l->tlb_snd_max, l->tlb_snd_una);
#ifdef NETFLIX_TCP_STACK
		if ((bbr->flex8 == TCP_HTTP_REQ_LOG_FREED) &&
		    ((bbr->flex3 & TCP_HTTP_TRACK_FLG_OPEN) == 0)) {
			/* calculate the bw req/to/comp */
			uint32_t conv_time;

			print_out_space(out);
			conv_time = (uint32_t)ltime;
			if (TSTMP_GT(bbr->timeStamp, conv_time)) {
				uint64_t btf, calc_bw;
				uint32_t tim;

				tim = bbr->timeStamp - conv_time;
				btf = (bbr->cur_del_rate - bbr->delRate);
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
#endif
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

static void
dump_out_lro_log(const struct tcp_log_bbr *bbr)
{
	if (bbr->flex8 != 22) {
		fprintf(out,
			"Frm:%d, app_c:%d app_l:%d, head:0x%lx(l:%u) m:0x%lx(l:%d) p_len:%u tlen:%d llim:%u tm:%d\n",
			bbr->flex8,
			bbr->flex3,
			bbr->flex7,
			bbr->delRate,
			bbr->flex5,
			bbr->cur_del_rate,
			bbr->flex2,
			bbr->flex4,
			bbr->flex1,
			bbr->flex6, bbr->pkts_out);
	} else {
		fprintf(out,
			"Frm:%d, queued:%d need_wake:%d inp_flags2:0x%x in_input:%d will_flush:%d\n",
			bbr->flex8,
			bbr->pkts_out,
			bbr->flex1,
			bbr->inflight,
			bbr->delivered,
			bbr->pacing_gain);
	}
	if (extra_print) {
		print_out_space(out);
		fprintf(out, "le_nxt_seq:%u m_nxt_seq:%u, le_th_ack:%u m_th_ack:%u, le_win:%u th_win:%u\n",
			bbr->epoch,
			ntohl(bbr->inflight),
			ntohl(bbr->lt_epoch),
			ntohl(bbr->delivered),
			ntohs(bbr->cwnd_gain),
			ntohs(bbr->pacing_gain));
		print_out_space(out);
		fprintf(out, "head_mflags:0x%lx head_arr_tstmp:0x%lx\n",
			bbr->delRate,
			bbr->rttProp);
	}

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
		fprintf(out, "PACER nxt_slot:%u prev_slot:%u cur_slot:%u at:%u rt:%lu onqueue:%u curtick:%u sleeptime:%u\n",
			bbr->flex1, bbr->flex3, bbr->flex2, bbr->flex4,
			bbr->cur_del_rate,
			bbr->flex6, bbr->flex5,
			bbr->lost
			);
		if (extra_print) {
			print_out_space(out);
			fprintf(out, "ttr:%u saved_prev_slot:%u saved_cur_slot:%u saved_curtick:%u delayed:%u sleep_override:%u\n",
				bbr->inflight,
				bbr->lt_epoch,
				bbr->epoch,
				bbr->delivered,
				bbr->pkts_out,
				bbr->applimited);

		}
	} else {
		fprintf(out, "Unknown diag %d\n", bbr->use_lt_bw);
	}
}

static uint32_t cwnd_enter_time = 0;

#ifdef NETFLIX_TCP_STACK
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

static void
handle_user_type_httpd(const struct tcp_log_buffer *l)
{
	const union tcp_log_userdata *data;

	data = (const union tcp_log_userdata *)&l->tlb_stackinfo.u_raw;
	/* tlb_flex2 has the subtype */
	switch (l->tlb_flex2) {
	case TCP_LOG_HTTPD_TS:
		fprintf(out, "ts: %"PRIu64 "\n", data->http_req.timestamp);
		break;
	case TCP_LOG_HTTPD_TS_REQ:
	{
		/* print timestamp */
		fprintf(out, "tm: %"PRIu64, data->http_req.timestamp);
		/* print range */
		fprintf(out, " range: [ ");
		if (data->http_req.flags & TCP_LOG_HTTPD_RANGE_START)
			fprintf(out, "%"PRIu64, data->http_req.start);
		fprintf(out, "-");
		if (data->http_req.flags & TCP_LOG_HTTPD_RANGE_END)
			fprintf(out, "%"PRIu64, data->http_req.end);
		/* The range request is inclusive so we add 1 */
		if ((data->http_req.flags & TCP_LOG_HTTPD_RANGE_END) &&
		    (data->http_req.flags & TCP_LOG_HTTPD_RANGE_START))
			fprintf(out, " (len:%lu)",
				((data->http_req.end - data->http_req.start) + 1));
		fprintf(out, " ]\n");
		break;
	}
	default:
		fprintf(out, "Unknown user subtype %u\n", l->tlb_flex2);
		break;
	}
}

static void
handle_user_type_unknown(const struct tcp_log_buffer *l)
{

	fprintf(out, "Unknown user type %u\n", l->tlb_flex1);
}

static void
handle_user_event_log_entry(const struct tcp_log_buffer *l)
{

	assert(l->tlb_eventid == TCP_LOG_USER_EVENT);
	/* tlb_flex1 has the type */
	switch (l->tlb_flex1) {
	case TCP_LOG_USER_HTTPD:
		handle_user_type_httpd(l);
		break;
	default:
		/* unknown type */
		handle_user_type_unknown(l);
		break;
	}
}
#endif

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
	is_bbr = 1;
	msg_types_list[id]++;
	if (l->tlb_eventid == TCP_LOG_RTO) {
		tlb_sn = l->tlb_sn;
		return;
	}
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
	if ((tlb_sn+1) != l->tlb_sn) {
		if (tlb_sn > l->tlb_sn) {
			duplicates++;
			return;
		}
		if (show_all_messages) {
			fprintf(out, "***Missing sn:%d -> l->tlb_sn:%d ****\n", tlb_sn, l->tlb_sn);
		}
		total_missed_records += (l->tlb_sn - tlb_sn);
	}
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
		dump_out_lro_log(bbr);
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
	case BBR_LOG_SRTT_GAIN_EVENT:
	{
		const char *method;
		char bogons[100];
		char *dr, *inuse;
		if (bbr->flex8 == 0)
			method = "Feature Disabled";
		else if (bbr->flex8 == 1)
			method = "Gaining";
		else if (bbr->flex8 == 2)
			method = "Continued Gain";
		else if (bbr->flex8 == 3)
			method = "Reducing";
		else if (bbr->flex8 == 4)
			method = "Neither";
		else if (bbr->flex8 == 5)
			method = "Release reduction";
		else {
			sprintf(bogons, "New Unknown %d", bbr->flex8);
			method = bogons;
		}
		inuse = display_bw(bbr->bw_inuse, 1);
		dr = display_bw(bbr->delRate, 1);
		fprintf(out, " %s:%u delta:%u ndelta:%u s7-srtt:%u s2-srtt:%u icnt:%u gain_cnt:%u red:%u DR:%s AR:%s\n",
			method, bbr->flex7,
			bbr->flex1, bbr->flex2,
			bbr->flex3, bbr->flex4,
			bbr->flex5, bbr->flex6, bbr->pkts_out, dr, inuse);
		if (inuse)
			free(inuse);
		if (dr)
			free(dr);
		break;
	}
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
#ifdef NETFLIX_TCP_STACK
	case TCP_LOG_USER_EVENT:
		if (show_all_messages) {
			handle_user_event_log_entry(l);
		}
		break;
	case TCP_LOG_SENDFILE:
		if (show_all_messages) {
			handle_sendfile_log_entry(l);
		}
		break;
#endif
	case BBR_LOG_EXTRACWNDGAIN:
		if (show_all_messages) {
			fprintf(out, "Addition from:%s extra_gain:%u acked_calc:%u\n",
				((bbr->flex8 == 1) ? "stretch ack" :  "compressed ack"),
				bbr->flex1, bbr->flex2);
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
	case TCP_SAD_DETECTION:
		dump_sad_values(bbr);
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
	case TCP_LOG_HTTP_T:
		tcp_display_http_log(l, bbr);
		break;
#ifdef NETFLIX_TCP_STACK
	case TCP_LOG_SB_WAKE:
		tcp_display_wakeup(l, bbr);
		break;
#endif
	case TCP_LOG_IN:
	{
		int off_len;
		uint32_t tasf;
		const char *ackflags;
		uint32_t acks;
		int have_ack;

		last_rwnd_at_out = l->tlb_snd_wnd;
		if (th) {
			ackflags = translate_flags(th->th_flags);
			have_ack = th->th_flags & TH_ACK;
			th_ack = ntohl(th->th_ack);
			th_seq = ntohl(th->th_seq);
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
		if (have_ack && SEQ_GT(th_ack, l->tlb_snd_una)) {
			acks = th_ack - l->tlb_snd_una;
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
					l->tlb_snd_una, th_ack, bbr->pkt_epoch, th_seq, l->tlb_rcv_nxt, tasf,
					bbr->flex6);
				print_out_space(out);
				fprintf(out, " m_flags:0x%x hwtsmp:%u(-%u) arrtstmp:%u(-%u) actual:%u lb:%u\n",
					bbr->flex3,
					bbr->lt_epoch, (bbr->pkts_out - bbr->lt_epoch),
					bbr->flex5, (bbr->pkts_out - bbr->flex5),
					bbr->pkts_out, bbr->flex2);

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
	case TCP_HDWR_TLS:
		if (bbr->flex8 == 0) {
			/* TCP m_copy_m logging */
			if (bbr->flex1)
				fprintf(out, "goal len:%d updated_len:%d mflags:0x%x mlen:%d off:%u\n",
					bbr->flex3, bbr->flex4, bbr->flex1, bbr->flex2, bbr->flex5);
			else
				fprintf(out, "Final target len:%d final:%d\n", bbr->flex3, bbr->flex4);
		} else {
			/* BBR logging */
			fprintf(out, "mode:%d len:%d rw:%u cwnd:%u avail:%u flight:%u out:%u olen:%u pseg:%u ca:%d\n",
				bbr->flex7, bbr->flex4,
				l->tlb_snd_wnd,
				l->tlb_snd_cwnd,
				l->tlb_txbuf.tls_sb_acc,
				bbr->inflight,
				(l->tlb_snd_max - l->tlb_snd_una),
				bbr->flex2, bbr->flex3, bbr->flex5);
		}
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
	case TCP_LOG_OUT:
	{
		const char *bwd;
		int sidx;
		int rec, drain, hot, ured, t_maxseg;
		int bw_override = 0;
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
		ured = bbr->flex2 & 0x1;
		t_maxseg = bbr->flex5 & 0x00ffffff;
		hot = (bbr->flex2 >> 1) & 0x1;
		drain = (bbr->flex2 >> 2) & 0x1;
		rec = (bbr->flex2 >> 3) & 1;
		if (bbr->bbr_state == BBR_STATE_PROBE_RTT)
			bw_override = 1;
		else if ((bbr->bbr_state == BBR_STATE_PROBE_BW) &&
			 ((bbr->bbr_substate == BBR_SUB_GAIN) ||
			  (bbr->bbr_substate == BBR_SUB_DRAIN)))
			bw_override = 1;
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
		} else {
			foo = ' ';
		}
		state_send_count++;
		state_send_bytes += l->tlb_len;
		sub = bbr->timeStamp - last_out_time;
		last_out_time = bbr->timeStamp;
		if (show_all_messages) {
			fprintf(out, "Sent(e:%d) %u:%u%c (%s:%d) flt:%u avail:%d (spo:%u ip:%d ii:%d rdhu:0x%x %s(%lu) pg:%u piw:%d pd:%d d:%d)\n",
				l->tlb_errno,
				th_seq, l->tlb_len, foo,
				translate_flags(th->th_flags), l->tlb_errno,
				bbr->inflight,
				l->tlb_txbuf.tls_sb_acc,
				sub, bbr->inhpts, bbr->ininput,
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
			fprintf(out, "Type:%s expires set_to:%u at line:%d (ip:%d ii:%d) out:%u cw:%u rw:%u pe:%u srtt:%u\n",
				timer_types[val],
				bbr->flex2,
				bbr->flex1,
				bbr->inhpts, bbr->ininput,
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
	case TCP_LOG_BAD_RETRAN:
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
				fprintf(out, "App?:%d DR:%s cDR:%s lt:%lu del:%u tim:%u (ip:%d ii:%d ult:%d) avail:%u\n",
					bbr->flex8,
					bw_str,
					cur_del_rate_str,
					bbr->bw_inuse,
					(bbr->delivered - bbr->flex6),
					(bbr->timeStamp - bbr->flex5),
					bbr->inhpts, bbr->ininput, bbr->use_lt_bw,
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
			fprintf(out, "DR:%s ltbw:%lu rttProp:%ld sent:%u pacing_slot:%u out:%u flight:%u cw:%u line:%d (ip:%d ii:%d ult:%d)\n",
				display_bw(bbr->delRate, 0),
				bbr->bw_inuse,
				bbr->rttProp,
				l->tlb_len,
				bbr->flex1,
				(l->tlb_snd_max - l->tlb_snd_una),
				bbr->inflight,
				l->tlb_snd_cwnd, bbr->flex4,
				bbr->inhpts, bbr->ininput, bbr->use_lt_bw);
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
			fprintf(out, "Avail:%u cw:%u rw:%u (ip:%d ii:%d ult:%d) rttProp:%ld %u st:%u\n",
				l->tlb_txbuf.tls_sb_acc,
				l->tlb_snd_cwnd,
				l->tlb_snd_wnd,
				bbr->inhpts,
				bbr->ininput,
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
			fprintf(out, "avail:%u cw:%u rw:%u (ip:%d ii:%d ult:%d) pe:%u cpu:%d nseg:%d p_cpu:0x%x\n",
				l->tlb_txbuf.tls_sb_acc,
				l->tlb_snd_cwnd,
				l->tlb_snd_wnd,
				bbr->inhpts, bbr->ininput, bbr->use_lt_bw,
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
				fprintf(out, "(ip:%d iip:%d ult:%d) rc:%d minto:%d t_rxtcur:%u(%u)\n",
					bbr->inhpts, bbr->ininput, bbr->use_lt_bw, bbr->flex4, bbr->flex5, bbr->flex6, calc_trxt);
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
				fprintf(out, " tp_flags:0x%x (ip:%d iip:%d ult:%d) rm_frm_pacer:%d\n",  l->tlb_flags,
					bbr->inhpts, bbr->ininput, bbr->use_lt_bw, bbr->flex8);
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
			fprintf(out, "out_from_line:%u rec:%d prtt:%d tot_len:%u p_maxseg:%u cw:%u rw:%u flight:%u out:%u avail:%u (ip:%d ii:%d ult:%d pc:%u) %s\n",
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
				bbr->inhpts, bbr->ininput, bbr->use_lt_bw, bbr->flex7, reascode);
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
			uint32_t gain, stayed, late = 0;

			if (avail_is_zero) {
				time_avail_zero += (bbr->timeStamp - time_saw_avail_zero);
				time_saw_avail_zero  = bbr->timeStamp;
			}
			gain = bbr->cwnd_gain;
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





static int use_timestamp = 1;
static uint64_t lost_rack_count = 0;

static uint32_t min_rtt_seen, max_rtt_seen;
static int32_t prev_rtt;
static int32_t rtt_diff = 0;
static uint8_t prtt_set = 0;
static uint8_t rtt_diff_set = 0;

static uint32_t last_rtt_measure = 0;
static uint32_t gp_srtt = 0;

static int32_t gp_prev_rtt;
static int32_t gp_rtt_diff = 0;
static uint8_t gp_prtt_set = 0;
static uint8_t gp_rtt_diff_set = 0;
static uint32_t gp_lower_rtt = 0;
static uint32_t last_cwnd_to_use = 0;

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
	msg_types_list[id]++;
	l_timeStamp = bbr->timeStamp;
	if (id == TCP_LOG_SOCKET_OPT) sock_opt_cnt++;
	if ((id == TCP_LOG_USERSEND) ||
	    (id == TCP_LOG_FLOWEND) ||
	    (id == TCP_LOG_CONNEND) ||
	    (id == TCP_LOG_USER_EVENT) ||
	    (id == TCP_LOG_SENDFILE) ||
	    (id == TCP_LOG_SOCKET_OPT)){
		l_timeStamp = (uint32_t) ((l->tlb_tv.tv_sec * HPTS_USEC_IN_SEC) + l->tlb_tv.tv_usec);
	}
	tlb_sn = l->tlb_sn;
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
		} else
			fprintf(out, "%u %u rack [%u] %s ",
				time_display, number_flow, timeoff, evt_name(id));
	}
	switch (id) {
	default:
	case TCP_LOG_BAD_RETRAN:
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
	case BBR_LOG_CWND:
	case BBR_LOG_BWSAMP:
	case BBR_LOG_MSGSIZE:
	case BBR_LOG_STATE:
		fprintf(out, " new msg %d?\n", id);
		break;
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
			"Line:%d ifp:0x%lx err:%d (DR:%s req_BW:%s hw_bw:%s) FH:0x%x\n",
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
	case BBR_LOG_HPTSI_CALC:
	{
		uint64_t bw_est, bw_raise, srtt;

		bw_est = bbr->bw_inuse;
		bw_raise = bbr->delRate;
		srtt = bbr->pkts_out;
		srtt <<= 32;
		srtt |= bbr->applimited;;
		if (bbr->flex8 == 1) {
			fprintf(out, "Setting GP INCR CA mult=%u, SS mult=%u REC mult:%lu line:%d minrtt:%u\n",
				bbr->flex1,
				bbr->flex2, bbr->bw_inuse, bbr->pkt_epoch, bbr->pkts_out);
		} else if (bbr->flex8 == 2) {
			uint64_t lentim;
			char *rbw;
			const char *ccmode;
			double multiplier;

			if (IN_RECOVERY(l->tlb_flags)) {
				ccmode = "REC";
				multiplier = (bbr->applimited  * 1.0);
			} else if (bbr->flex7 == 0) {
				ccmode = "CA";
				multiplier = (bbr->flex6 * 1.0);
			} else {
				ccmode = "SS";
				multiplier = (bbr->flex5 * 1.0);
			}
			fprintf(out, "mode:%d len:%u slot:%u min_seg:%u max_seg:%u gain:%u min_rtt:%u smRSC:0x%x\n",
				bbr->flex8,
				bbr->flex2,
				bbr->flex1, bbr->flex3, bbr->flex4, bbr->pacing_gain, bbr->pkts_out, bbr->cwnd_gain);
			lentim = bbr->rttProp;
			rbw = display_bw(bw_raise, 1);
			print_out_space(out);
			fprintf(out, " bw_est:%s (%lu) actual_bw:%s (%lu) multiplier:%2.3f%% (%s) avail:%u\n",
				display_bw(bw_est, 0),
				bw_est,
				rbw,
				bw_raise, multiplier, ccmode,
				l->tlb_txbuf.tls_sb_acc);
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
			bytes_ps = (uint64_t)bbr->flex2;
			bytes_ps *= 1000000;
			bytes_ps /= tim;
			/* Our new GP estimate (updated) is in lentime aka rttProp */
			gbw = display_bw(bbr->rttProp, 1);
			bwest = display_bw(bytes_ps, 1);
			fprintf(out, "GP est TIMELY gput:%s(%lu) new GP value %s(%lu) [len:%u tim:%u%s stim:%lu%s] minrtt:%u gain:%u AGSP:0x%x  RSC:0x%x\n",
				bwest,
				bytes_ps,
				gbw,
				bbr->rttProp,
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
				fprintf(out, "t_flags:0x%x\n", l->tlb_flags);
			}
		} else  if (bbr->flex8 == 5) {
			fprintf(out, "Change GP range oldts:%u newts:%u oldseq:%lu newseq:%lu line:%u AGSP:0x%x\n",
				bbr->flex2, bbr->flex1,
				bbr->bw_inuse, bbr->delRate,
				bbr->pkt_epoch, bbr->use_lt_bw);
		} else  if (bbr->flex8 == 6) {
			fprintf(out, "Aborted measurment app limited case reduced to %u bytes AGSP:0x%x\n",
				bbr->flex2 - bbr->flex1, bbr->use_lt_bw);
		} else  if (bbr->flex8 == 7) {
			fprintf(out, "Old rack burst mitigation len:%u slot:%u trperms:%lu reduce:%lu minrtt:%u\n",
				bbr->flex2, bbr->flex1, bbr->bw_inuse, bbr->delRate, bbr->pkts_out);
		} else if (bbr->flex8 == 8) {
			fprintf(out, "Setting Fixed Pacing CA mult=%u, SS mult=%u REC mult:%lu line:%d minrtt:%u\n",
				bbr->flex1,
				bbr->flex2, bbr->bw_inuse, bbr->pkt_epoch, bbr->pkts_out);
		} else  if (bbr->flex8 == 9) {
			fprintf(out, "GP Measure to_ack:%u frm_seq:%u (len:%u) snd_una:%u snd_max:%u rsm:0x%lx alc:%lu LINE:%d AGSP:0x%x\n",
				bbr->flex1, bbr->flex2, (bbr->flex1 - bbr->flex2),
				l->tlb_snd_una,
				l->tlb_snd_max,
				bbr->bw_inuse,
				bbr->rttProp, bbr->pkt_epoch,
				bbr->use_lt_bw);
			if (extra_print) {
				print_out_space(out);
				fprintf(out, "start_ts:%lu minrtt:%u\n",
					bbr->delRate, bbr->pkts_out);
			}
		} else  if (bbr->flex8 == 10) {
			fprintf(out, "Aborted measurment too short req:%u actual:%u AGSP:0x%x line:%d\n",
				bbr->flex1, bbr->flex2, bbr->use_lt_bw,
				bbr->pkt_epoch);
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
		} else if (bbr->flex8 == 15) {
			fprintf(out, "Setting pacing max seg set was %lu now at %u line:%u minrtt:%u\n",
				bbr->bw_inuse, bbr->flex4, bbr->pkt_epoch, bbr->pkts_out);
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
			fprintf(out, "EXIT RECOVERY cwnd:%u-to->%u ssthresh:%u\n",
				bbr->pkts_out, l->tlb_snd_wnd, l->tlb_snd_ssthresh);
		} else {
		fprintf(out, "PRR UPDATE frm:%d out:%u recover_fs:%u sndcnt:%u del:%u sacked:%u holes:%u ssthresh:%u out:%u t_flags:0x%x\n",
			bbr->flex8,
			bbr->flex1,
			bbr->flex2,
			bbr->flex3,
			bbr->flex4,
			bbr->flex5, bbr->flex6,
			l->tlb_snd_ssthresh,
			(l->tlb_snd_max - l->tlb_snd_una), l->tlb_flags);
		}
		break;
	case TCP_LOG_LRO:
		dump_out_lro_log(bbr);
		break;
	case TCP_SACK_FILTER_RES:
		dump_sack_filter(bbr);
		break;
	case TCP_SAD_DETECTION:
		dump_sad_values(bbr);
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
			fprintf(out, "do:%d np:%d wo:%d in_per:%d (ip:%d) tmrs:%s sndcnt:%u way_out:%d out:%u state:%u rw:%d (%c%u)\n",
				bbr->flex1,
				bbr->flex2,
				bbr->flex7,
				bbr->flex8,
				bbr->inhpts,
				mask, bbr->flex5,
				bbr->flex3,
				(l->tlb_snd_max - l->tlb_snd_una),
				l->tlb_state, l->tlb_snd_wnd, sign, chg);
			if (extra_print) {
				print_out_space(out);
				fprintf(out, "avail:%u inq:%u\n",
					l->tlb_txbuf.tls_sb_acc,
					l->tlb_rxbuf.tls_sb_acc);
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
	case TCP_LOG_RTT:
		fprintf(out, " rtt:%u applied to srtt %u var %u t_flags:%x cw:%u\n",
			bbr->flex1,
			((l->tlb_srtt * 1000) >> TCP_RTT_SHIFT),
			((l->tlb_rttvar * 1000) >> TCP_RTT_SHIFT),
			l->tlb_flags, l->tlb_snd_cwnd);
		print_out_space(out);
		fprintf(out, "sd:%d ackcnt:%u sackcnt:%u nomove:%u move:%u sst:%u\n",
			bbr->flex8,
			bbr->flex2, bbr->flex3,
			bbr->flex4,
			bbr->flex5, l->tlb_snd_ssthresh);
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
			fprintf(out, "type:%s(%s:%x) srtt:%d for %u(%u) cw:%u rw:%u (ip:%d iip:%d) slot:%d frm:%d\n",
				mask,
				which_one, bbr->flex3,
				bbr->flex1,
				bbr->flex2, bbr->flex4,
				l->tlb_snd_cwnd, l->tlb_snd_wnd,
				bbr->inhpts, bbr->ininput,
				bbr->flex5, bbr->flex8);
			print_out_space(out);
			fprintf(out, "t_rxtcur:%u state:%u (u:%u m:%u a:%u pers:%d) line:%d\n",
				bbr->flex6, l->tlb_state,
				l->tlb_snd_una, l->tlb_snd_max,
				l->tlb_txbuf.tls_sb_acc,
				bbr->flex7, bbr->pkts_out);
			if (bbr->flex3 & PACE_TMR_KEEP) {
				print_out_space(out);
				fprintf(out, "KEEP:Sent so far:%u\n",
					(l->tlb_snd_max - l->tlb_iss));
			}
		}
		break;
	case BBR_LOG_TIMERCANC:
		mask = get_timer_mask(bbr->flex3);
		if (bbr->flex8 == 1) {
			fprintf(out, "type:%s cw:%u rw:%u tp_flags:0x%x (ip:%d iip:%d) rm_frm_pacer:%d state:%u hpts_flgs:%d line:%d\n",
				mask,
				l->tlb_snd_cwnd, l->tlb_snd_wnd,
				l->tlb_flags,
				bbr->inhpts, bbr->ininput,
				bbr->flex7, l->tlb_state,
				bbr->flex3, bbr->flex1
				);
			print_out_space(out);
			fprintf(out, "last_output_to:%u now:%u prr:%u sst:%u flight:%u\n",
				bbr->flex2, bbr->flex4, bbr->flex5,
				l->tlb_snd_ssthresh, bbr->inflight);
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
		}
		break;
	case BBR_LOG_BBRSND:
		fprintf(out, "slot:%u (ip:%d ii:%d) state:%u t_flags:0x%x prr:%d\n",
			bbr->flex1, bbr->inhpts, bbr->ininput, l->tlb_state, l->tlb_flags, bbr->flex2);
		break;
	case BBR_LOG_JUSTRET:
	{
		const char *reascode;

		last_cwnd_to_use = bbr->lt_epoch;
		reascode = get_jr_reason(bbr->flex4);
		fprintf(out, "slot:%u (ip:%d ii:%d pc:%d) in_persist:%d avail:%u scw:%u rw:%u out:%u state:%u sndcnt:%d cw:%u reas:%s\n",
			bbr->flex1, bbr->inhpts, bbr->ininput,
			bbr->flex7, bbr->flex8,
			l->tlb_txbuf.tls_sb_acc,
			bbr->lt_epoch,
			l->tlb_snd_wnd,
			(l->tlb_snd_max - l->tlb_snd_una),
			l->tlb_state, bbr->flex5, l->tlb_snd_cwnd, reascode);
		if (extra_print) {
			print_out_space(out);
			mask = get_timer_mask(bbr->flex2);
			fprintf(out, "snd_una:%u snd_nxt:%u snd_max:%u sb_off:%u tmr:0x%x (%s) t_flags:0x%x\n",
				l->tlb_snd_una, l->tlb_snd_nxt, l->tlb_snd_max,
				(l->tlb_snd_nxt - l->tlb_snd_una), bbr->flex2, mask, l->tlb_flags);
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
#ifdef NETFLIX_TCP_STACK
	case TCP_LOG_USER_EVENT:
		handle_user_event_log_entry(l);
		break;
	case TCP_LOG_SENDFILE:
		handle_sendfile_log_entry(l);
		break;
#endif
	case BBR_LOG_HPTSDIAG:
		/*
		 * The pacer diag abuses 3 bbr fields to transfer
		 * all insert pacer information.
		 */
		if (show_all_messages) {
			show_pacer_diag(bbr);
		}
		break;
	case TCP_LOG_HTTP_T:
		tcp_display_http_log(l, bbr);
		break;
#ifdef NETFLIX_TCP_STACK
	case TCP_LOG_SB_WAKE:
		tcp_display_wakeup(l, bbr);
		break;
#endif
	case TCP_LOG_IN:
	{
		uint32_t lro_time;
		int off_len;
		uint16_t rw_in;
		uint32_t acks;
		const char *ackstate, *datastate;
		int have_ack;

		last_rwnd_at_out = l->tlb_snd_wnd;
		if (th) {
			have_ack = th->th_flags & TH_ACK;
			th_ack = ntohl(th->th_ack);
			th_seq = ntohl(th->th_seq);
			rw_in = ntohs(th->th_win);
			off_len = th->th_off << 2;
		} else {
			have_ack = 0;
			off_len = 0;
			th_ack = 0xbadbad;
			th_seq = 0xbadbad;
		}
		if (!have_ack) {
			acks = 0;
			ackstate = "none";
		} else if (SEQ_GT(th_ack, l->tlb_snd_una)) {
			acks = th_ack - l->tlb_snd_una;
			ackstate = "new";
		} else {
			acks = 0;
			if (th_ack ==  l->tlb_snd_una)
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
		if (bbr->flex3 & M_TSTMP) {
			lro_time = bbr->lt_epoch;
		}
		else if (bbr->flex3 & M_TSTMP_LRO) {
			lro_time = bbr->flex5;
		} else {
			lro_time = l_timeStamp;
		}
		if (rack_last_in_set == 0) {
			rack_last_in = l_timeStamp;
			rack_last_in_set = 1;
		}
		if(rack_arr_in_set == 0) {
			rack_arr_in = lro_time;
			rack_arr_in_set = 1;
		}
		fprintf(out, "Acks %u (%s) off:%u out:%u lenin:%u cw:%u rw:%u una:%u ack:%u t_flags:0x%x(%s,%s)\n",
			acks,
			translate_flags(th->th_flags),
			off_len,
			(l->tlb_snd_max - l->tlb_snd_una),
			l->tlb_len,
			l->tlb_snd_cwnd,
			l->tlb_snd_wnd,
			l->tlb_snd_una,
			th_ack, l->tlb_flags,
			ackstate, datastate);
		print_out_space(out);
		fprintf(out, "(ip:%d) state:%d t_flags:%x prr:%u\n",
			bbr->inhpts, l->tlb_state, l->tlb_flags, bbr->flex1);
		rack_sab_sum += (lro_time - rack_last_in);
		if (extra_print) {
			print_out_space(out);
			mask = get_timer_mask(bbr->flex4);
			fprintf(out, "mflags:0x%x nxt_pkt:%d hwts=0x%x ats:0x%x hpts_flags:%s(%x) mapa:%u\n",
				bbr->flex3,
				bbr->flex8,
				bbr->lt_epoch,
				bbr->flex5,
				mask,
				bbr->flex4, bbr->flex2);
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
			fprintf(out, " snd_una:%u snd_max:%u iss:%u sabsum:%lu arrvtsmp:%u (spa:%u ar_spa:%u)\n",
				l->tlb_snd_una,
				l->tlb_snd_max,
				l->tlb_iss, rack_sab_sum, lro_time,
				(lro_time - rack_arr_in),
				(l_timeStamp - rack_last_in));
			print_out_space(out);
			fprintf(out, "avail:%u inq:%u COcR:0x%x (ticks:%u start_tm:%u ago:%u)\n",
				l->tlb_txbuf.tls_sb_acc,
				l->tlb_rxbuf.tls_sb_acc,
				bbr->applimited,
				l->tlb_starttime,
				l->tlb_ticks, (l->tlb_ticks - l->tlb_starttime));
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
	case TCP_HDWR_TLS:
		if (bbr->flex8 == 0) {
			/* TCP m_copy_m logging */
			if (bbr->flex1)
				fprintf(out, "goal len:%d updated_len:%d mflags:0x%x mlen:%d off:%u\n",
					bbr->flex3, bbr->flex4, bbr->flex1, bbr->flex2, bbr->flex5);
			else
				fprintf(out, "Final target len:%d final:%d\n", bbr->flex3, bbr->flex4);
		} else if (bbr->flex8 == 1) {
			/* BBR logging */
			fprintf(out, "mode:%d len:%d rw:%u cwnd:%u avail:%u out:%u olen:%u mins:%u maxs:%u sacked:%u\n",
				bbr->flex7, bbr->flex4,
				l->tlb_snd_wnd,
				l->tlb_snd_cwnd,
				l->tlb_txbuf.tls_sb_acc,
				(l->tlb_snd_max - l->tlb_snd_una),
				bbr->flex5,
				bbr->flex1, bbr->flex3, bbr->flex6);
		} else {
			fprintf(out, "PACE SIZE SET min:%u max:%u opt_tls_siz:%u oh:%u frm:%u\n",
				bbr->flex1,
				bbr->flex3,
				bbr->flex4, bbr->flex5, bbr->flex8);
		}
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
			fprintf(out, " RACK RTR Reason:%s (%u) start:%u end:%u dupack:%u flags:0x%x\n",
				foo,
				bbr->flex8,
				bbr->flex5, bbr->flex6,
				bbr->flex4, bbr->flex3);
		else
			fprintf(out, " RACK RTR Reason:%s (%u) start:%u end:%u dupack:%u flags:0x%x line:%d\n",
				foo,
				bbr->flex8,
				bbr->flex5, bbr->flex6,
				bbr->flex4, bbr->flex3, bbr->flex1);

		break;
	}
	case TCP_LOG_OUT:
	{
		const char *rtr;
		char *bwd;
		if (th) {
			th_ack = ntohl(th->th_ack);
			th_seq = ntohl(th->th_seq);
		} else {
			th_ack = 0xbadbad;
			th_seq = 0xbadbad;
		}
		rtr = " ";
		last_cwnd_to_use = bbr->lt_epoch;
		bwd = display_bw(bbr->bw_inuse, 0);
		if (bbr->flex8) {
			rtr = "*";
			lost_rack_count += l->tlb_len;
		}
		fprintf(out, "Sent(%d) %u:%u%s (%s f:%d) bw:%s(%lu) avail:%d cw:%u scw:%u rw:%u flt:%u (spo:%u ip:%d)\n",
			l->tlb_errno,
			th_seq, l->tlb_len, rtr,
			translate_flags(th->th_flags), ((bbr->flex5 & 0x80000000) ? 1 : 0),
			bwd, bbr->bw_inuse,
			l->tlb_txbuf.tls_sb_acc,
			l->tlb_snd_cwnd,
			bbr->lt_epoch,
			l->tlb_snd_wnd, bbr->inflight,
			(time_to_use - rack_last_out), bbr->inhpts);
		if (extra_print) {
			print_out_space(out);
			fprintf(out, "state:%u srtt:%u pace min:%u max:%u t_flags:0x%x orig_len:%u mark:%u flight:%u inq:%u\n",
				l->tlb_state, (l->tlb_srtt >> TCP_RTT_SHIFT),
				bbr->flex2, bbr->flex3, l->tlb_flags, bbr->flex4, bbr->flex7, bbr->inflight,
				l->tlb_rxbuf.tls_sb_acc);
			print_out_space(out);
			fprintf(out, "Min seg:%u Max seg:%u agg_delay:%u agg_early:%u th_ack:%u out:%u sst:%u iss:%u sal:%d sndcnt:%d\n",
				bbr->flex2, bbr->flex3, bbr->applimited, bbr->flex6, th_ack,
				(l->tlb_snd_max - l->tlb_snd_una),
				l->tlb_snd_ssthresh, l->tlb_iss, bbr->delivered, bbr->flex1);
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
				"Timely Increase GP mask:0x%x ss:%u ca:%u rec:%u incr_per:%lu [lup:%d ldw:%d ASIR:0x%x] bw:%s(%lu) DRSC:0x%x\n",
				bbr->flex1,
				bbr->flex4,
				bbr->flex5,
				bbr->flex6, bbr->cur_del_rate,
				bbr->flex3, bbr->flex7, bbr->flex2, gpbw, bbr->rttProp, bbr->cwnd_gain
				);
		} else if (bbr->flex8 == 2) {
			char *gpbw;
			uint32_t ca_red, ss_red, rec_red;

			ca_red = (bbr->bw_inuse & 0x00000000ffffffff);
			ss_red = ((bbr->bw_inuse >> 32) & 0x00000000ffffffff);
			rec_red = (bbr->cur_del_rate & 0x00000000ffffffff);
			gpbw = display_bw(bbr->rttProp, 0);
			fprintf(out,
				"Timely Decrease GP mask:0x%x ss:%u ca:%u rec:%u redca:%u redss:%u redrec:%u [lup:%d ldw:%d ASIR:0x%x] bw:%s(%lu) DRSC:0x%x\n",
				bbr->flex1,
				bbr->flex4,
				bbr->flex5,
				bbr->flex6,
				ca_red, ss_red, rec_red,
				bbr->flex3, bbr->flex7, bbr->flex2,
				gpbw, bbr->rttProp, bbr->cwnd_gain
				);
		} else if (bbr->flex8 == 3) {
			char *gbw, *lbw, *ubw;

			lbw = display_bw(bbr->delRate, 1);
			gbw = display_bw(bbr->cur_del_rate, 1);
			ubw = display_bw(bbr->bw_inuse, 1);
			fprintf(out,
				"Timely comparison timely:%s(%u) low_bnd:%s(%lu) < cur_bw:%s(%lu) < up_bnd:%s(%lu) [lup:%d ldw:%d ASIR:0x%x] line:%d\n",
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
				"Timely calc timely:%s(%u) (rtt above max) rtt:%u > threshold:%u low_rtt:%lu prtt:%u rtt_diff:%d\n",
				(bbr->flex1 ? "DEC" : "INC"), bbr->flex1,
				rtt, threshold,
				bbr->delRate,
				lprev_rtt, my_rtt_diff);
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
				"Timely calc timely:%s(%d) (rtt below min) rtt:%u <  threshold:%u low_rtt:%lu prtt:%u rtt_diff:%d\n",
				(bbr->flex1 ? "DEC": "INC"), bbr->flex1,
				rtt, threshold,
				bbr->delRate,
				lprev_rtt, my_rtt_diff);
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
				"Timely calc timely:%s(%d) (gradient based) rtt:%u low_rtt:%lu prtt:%u rtt_diff:%d\n",
				(bbr->flex1 ? "DEC": "INC"), bbr->flex1,
				rtt,
				bbr->delRate,
				lprev_rtt, my_rtt_diff);
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
				"Timely %s mul:%d cur_bw:%s(%lu) cur_rate:%s(%lu) max_rate:%s(%lu)\n",
				((bbr->flex8 == 8) ? str1 : str2),
				bbr->flex1,
				cbw, bbr->cur_del_rate,
				cr, bbr->delRate,
				mr, bbr->bw_inuse);
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
			fprintf(out, "Off times new_per:%u alt:%u rtt:%u rtt_diff:%d gp_rtt_mul:%u minrtt:%u\n",
				new_per, alt,
				rtt, mrtt_diff,
				gp_rtt_mul, minrtt);
		} else if (bbr->flex8 == 11) {
			char *gpbw;

			gpbw = display_bw(bbr->rttProp, 0);
			fprintf(out,
				"Timely Lost b/w no-chg ss:%u ca:%u rec:%u [lup:%d ldw:%d ASIR:0x%x] bw:%s(%lu) DRSC:0x%x\n",
				bbr->flex4,
				bbr->flex5,
				bbr->flex6,
				bbr->flex3, bbr->flex7, bbr->flex2, gpbw, bbr->rttProp, bbr->cwnd_gain
				);

		} else if (bbr->flex8 == 12) {
			char *gpbw;

			gpbw = display_bw(bbr->rttProp, 0);
			fprintf(out,
				"Timely Gained b/w no-chg ss:%u ca:%u rec:%u [lup:%d ldw:%d ASIR:0x%x] bw:%s(%lu) DRSC:0x%x\n",
				bbr->flex4,
				bbr->flex5,
				bbr->flex6,
				bbr->flex3, bbr->flex7, bbr->flex2, gpbw, bbr->rttProp, bbr->cwnd_gain
				);
		} else {
			fprintf(out, " Unknown Timely log %d\n", bbr->flex8);
		}
		break;
	case BBR_LOG_RTO:
		val = bbr->flex8;

		if (val == 0xff) {
			fprintf(out, "User Closes inp:%d ini:%d state:%d newstate:%d so_error:%d\n",
				bbr->inhpts,
				bbr->ininput,
				bbr->flex1,
				bbr->flex2,
				bbr->flex3);
		} else {
			if (val > 6)
				val = 0;
			fprintf(out, "Type:%s min_rtt:%u rack_rtt:%u out:%u cw:%u rw:%u t_flags:0x%x out:%d (ip:%d) state:%u prr:%u\n",
				timer_types[val],
				bbr->flex1,
				bbr->flex2,
				(l->tlb_snd_max - l->tlb_snd_una),
				l->tlb_snd_cwnd,
				l->tlb_snd_wnd, l->tlb_flags,
				(l->tlb_snd_max - l->tlb_snd_una), bbr->inhpts, l->tlb_state, bbr->flex5);
		}
		break;
	case BBR_LOG_BBRRTT:
	{
		int32_t new_rtt_diff;
		double norm_grad;
		const char *override;

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
		fprintf(out, "rtt:%u len:%u avail:%u flight:%u (ip:%d) state:%u prr:%u NG:%f(%s) conf:%u\n",
			bbr->flex1,
			bbr->flex2,
			l->tlb_txbuf.tls_sb_acc,
			bbr->inflight,
			bbr->inhpts, l->tlb_state, bbr->pkts_out,
			norm_grad, ((norm_grad <= 0.0) ? "INC" : "DEC"), bbr->flex7
			);
		if (extra_print) {
			print_out_space(out);
			fprintf(out, " cw:%u sst:%u start:%u end:%u rtt_diff:%d nrtt_diff:%d %s f4:%u f5:%u\n",
				l->tlb_snd_cwnd, l->tlb_snd_ssthresh,
				bbr->pkt_epoch, bbr->lost,
				rtt_diff, new_rtt_diff, override, bbr->flex4,
				bbr->flex5);
			print_out_space(out);
			fprintf(out,
				"tar:%u prtt_st:%u flags:0x%x (Hibuf,Fora,Gpdy,Inprtt,Measaw,Appl,GPfill,Dragged)\n",
				bbr->applimited,
				bbr->epoch,
				bbr->use_lt_bw);
			print_out_space(out);
			fprintf(out,
				"prtt_en:%u (ago:%u) gain:%u low_rtt_us:%lu gp_srtt:%lu\n",
				bbr->lt_epoch,
				(bbr->timeStamp - bbr->lt_epoch),
				bbr->pacing_gain,
				bbr->cur_del_rate,
				bbr->delRate);
		}
		break;
	}
	};
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
#ifdef NETFLIX_TCP_STACK
	const struct tcp_log_raw *log;
#endif
	struct tcpopt to;

	if (l->tlb_eventid == BBR_LOG_RTT_SHRINKS) {
		dump_log_entry(l, th);
		force_bbr = 1;
		return;
	}
	if (l->tlb_eventid == TCP_LOG_RTO) {
		tlb_sn = l->tlb_sn;
		return;
	}
	bbr = &l->tlb_stackinfo.u_bbr;
#ifdef NETFLIX_TCP_STACK
	log = &l->tlb_stackinfo.u_raw;
#endif
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
	msg_types_list[id]++;
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
	case TCP_LOG_BAD_RETRAN:
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
		dump_out_lro_log(bbr);
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
			fprintf(out, "type:%s(%s) srtt:%d for %u(%u) cw:%u rw:%u (ip:%d iip:%d) rc:%d hpts_slot:%d t_rxtcur:%u frm:%d\n",
				mask,
				which_one,
				bbr->flex1,
				bbr->flex2, bbr->flex4,
				l->tlb_snd_cwnd, l->tlb_snd_wnd,
				bbr->inhpts, bbr->ininput,
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
#ifdef NETFLIX_TCP_STACK
	case TCP_LOG_USER_EVENT:
		handle_user_event_log_entry(l);
		break;
	case TCP_LOG_SENDFILE:
		handle_sendfile_log_entry(l);
		break;
#endif
	case TCP_LOG_HTTP_T:
		tcp_display_http_log(l, bbr);
		break;
	case TCP_LOG_IN:
	{
		if (th) {

			th_ack = ntohl(th->th_ack);
			th_seq = ntohl(th->th_seq);
			off_len = th->th_off << 2;
		} else {
			off_len = 0;
			th_ack = 0xbadbad;
			th_seq = 0xbadbad;
		}
		fprintf(out, "Acks %u (%s) off:%u out:%u lenin:%u avail:%u cw:%u rw:%u th_seq:%u una:%u th_ack:%u rto:%u srtt:%u state:%d\n",
			(th_ack - l->tlb_snd_una),
			translate_flags(th->th_flags),
			off_len,
			(l->tlb_snd_max - l->tlb_snd_una),
			l->tlb_len,
			l->tlb_txbuf.tls_sb_acc,
			l->tlb_snd_cwnd,
			l->tlb_snd_wnd,
			th_seq,
			l->tlb_snd_una,
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
	case TCP_LOG_OUT:
	{
		char rtr;
		const char *flags_out;
		if (th) {
			th_ack = ntohl(th->th_ack);
			th_seq = ntohl(th->th_seq);
			off_len = th->th_off << 2;
			flags_out = translate_flags(th->th_flags);
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
}

static int force_rack=0;
static int force_default=0;

static uint32_t stack_cnts[10];
static int print_out_time_offset = 0;
static struct tcp_log_buffer aux_buf;

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
		if (surpress && strcmp(stackname, surpress))
			continue;
		if (dump_sn) {
			fprintf(out, "%s:%d", stackname,
				lbufp->tlb_stackid);
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
	while ((i = getopt(argc, argv, "A:b:d:D:ef:Fi:lL:mMN:o:OprRs:S:tTUw:WxYzZ:?")) != -1) {
		switch (i) {
		case 'A':
			record_num_start = strtoul(optarg, NULL, 0);
			num_start_set = 1;
			break;
		case 'b':
			first_time = strtoul(optarg, NULL, 0);
			first_time_set = 1;
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
			/* Surpress all but this guy */
			surpress = optarg;
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
			fprintf(stderr, " -c - non condensed Record marks\n");
			fprintf(stderr, " -d directory-where-files-are (default=/var/log/tcplog_dumps)\n");
			fprintf(stderr, " -D file - specify a file to dump sack logging information to\n");
			fprintf(stderr, " -e - enable extra printing\n");
			fprintf(stderr, " -f stackname - Force interpret to this stack name\n");
			fprintf(stderr, " -F add file name in output\n");
			fprintf(stderr, " -i sessionid - display the specified session\n");
			fprintf(stderr, " -l don't log all state transistions don't collapse the probe_bw neutral ones\n");
			fprintf(stderr, " -L cnt - Set a maximum of cnt limit to the number of .xz files to read\n");
			fprintf(stderr, " -m - show message stats summary at the end\n");
			fprintf(stderr, " -N num - place flow-num after the time (def=0)\n");
			fprintf(stderr, " -o output - direct output to this file not stdout\n");
			fprintf(stderr, " -O condense message output showing minimal information\n");
			fprintf(stderr, " -r relative time on\n");
			fprintf(stderr, " -R - Show record numbers at the edge of the trace\n");
			fprintf(stderr, " -s stack - surpress the printing of all but this stacks info\n");
			fprintf(stderr, " -S num - Don't start at file number 0, start at num\n");
			fprintf(stderr, " -t print out the time too\n");
			fprintf(stderr, " -T -- For rack don't use the bbr->timestamp field (usecs) and use ticks\n");
			fprintf(stderr, " -U include user send events in the display\n");
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
	if (out != stdout)
		fclose(out);
	if (show_msg_stats) {
		for(i=0; i<MAX_TYPES; i++) {
			if (msg_types_list[i])
				fprintf(stderr, "Type %s(%d) had %d msgs\n",
					log_names[i],
					i, msg_types_list[i]);
		}
	}
	return(0);
}
