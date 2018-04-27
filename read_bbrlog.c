#include <sys/types.h>
#include <stdio.h>
#include <stdlib.h>
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
#include <net/route.h>
#include <netinet/tcp_seq.h>
#include <netinet/tcp_var.h>

#include <assert.h>

#include <bbparse.h>

static FILE *dump_out_sack=NULL;
#define	MAX_TYPES  TCP_LOG_END
static int extra_print = 0;
static int number_flow = 0;
static const char *surpress=NULL;

static uint32_t time_in_hot = 0;
static int lesser_is_hot = 0;
static uint32_t lesser_goes_hot = 0;

static int print_out_the_time = 0;
static int show_all_messages=1;
static uint32_t out_count = 0;
static int display_file_names = 0;
static uint32_t warn_behind=0;

static const char *dirname = "/var/log/tcplog_dumps";
static uint32_t epoch_lost = 0;
static uint32_t epoch_delivered = 0;
static uint32_t first_time=0;
static int first_time_set=0;
static int time_is_relative = 0;


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

#define BBR_PKT_OUTPUT 0x01	/* Output Packets being paced */
#define BBR_TMR_RACK   0x02	/* RACK timer running */
#define BBR_TMR_TLP    0x04	/* TLP timer running */
#define BBR_TMR_RXT    0x08	/* Retransmit timer running */
#define BBR_TMR_PERSIT 0x10	/* Persists timer running */
#define BBR_TMR_KEEP   0x20	/* Keep alive timer running */
#define BBR_TMR_DELACK 0x40	/* Delayed ack timer running */
#define BBR_TMR_MASK   (BBR_TMR_KEEP|BBR_TMR_PERSIT|BBR_TMR_RXT|BBR_TMR_TLP|BBR_TMR_RACK|BBR_TMR_DELACK)

static uint32_t msg_types_list[MAX_TYPES];

static uint64_t total_missed_records = 0;
static const char *log_names[MAX_TYPES] = {
	"UNKNOWN           ",
	"IN        ", /* Incoming packet                 1 */
	"PKT_OUT   ", /* Transmit (without other event)  2 */
	"RTO       ", /* Retransmit timeout              3 */
	"TF_ACK    ", /* Transmit due to TF_ACK          4 */
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
	"CWND      ", /* Cwnd change                      17 */
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
	"UNUSED_32 ", /* Unused                           32 */
	"UNUSED_33 ", /* Unused                           33 */
	"EPOCH_TIME", /* A timed based Epoch occured      34 */
	"LOG_TO_PRO", /* A to was processed               35 */
	"TSO_SZ_UPD", /* Update the TSO size              36 */
	"PACERDIAG ", /* A pacer diag msg                 37 */
	"LOWGAIN   ", /* Log a low gain event             38 */
	"PROGRESS  ", /* A progress event		  39 */
	"TCP_OPTION", /* A tcp option is set		  40 */
	"BBR_LOG_TIMERPREP", /* timing calc check         41 */
	"BBR_ENOBUF_JMP",	/* 42 */
	"BBR_PACING_CALC",	/* 43 */
	"BBR_RTT_SHRINKS",	/* 44 */
	"BBR_LOG_BW_RED_EV",     /* 45 */
        "BBR_STARTUP_LOG",     /* 46 */
	"TCP_LOG_RTT",	       /* 47 */
	"BBR_SETTINGS"		/* 48 */
};

static uint32_t time_last_setting = 0;
static int last_set_set=0;

static uint32_t last_ack_time = 0;
static uint32_t last_out_time = 0;
static uint32_t last_input_time = 0;
static uint32_t last_pg_chg=0;
static uint32_t opg=0;
static uint32_t last_evt_time=0;

#define REASON_MAX 7
static const char *lt_bw_reasons[REASON_MAX] = {
	"Stop using lt bw", 		/* 0 */
	"Begin sampling lt bw",		/* 1 */
	"App Limit reset sample",	/* 2 */
	"Been too long reset sampling", /* 3 */
	"Being Policed use lt bw",	/* 4 */
	"Saved a lt bw sample",		/* 5 */
	"Unknown"			/* 6 */
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
	if (tmask & BBR_TMR_DELACK) {
		strcat(mask_value, "DACK");
		outr = 1;
	} else 	if (tmask & BBR_TMR_RACK) {
		strcat(mask_value, "RACK");
		outr = 1;
	} else 	if (tmask & BBR_TMR_TLP) {
		strcat(mask_value, "TLP");
		outr = 1;
	} else if (tmask & BBR_TMR_RXT) {
		strcat(mask_value, "RXT");
		outr = 1;
	} else if (tmask & BBR_TMR_PERSIT) {
		strcat(mask_value, "PER");
		outr = 1;
	} else if (tmask & BBR_TMR_KEEP) {
		strcat(mask_value, "KEEP");
		outr = 1;
	} 
	if (tmask & BBR_PKT_OUTPUT) {
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

static const char *major_state[5] = {
	"UNKNOWN STATE",
	"BBR_STATE_STARTUP",
	"BBR_STATE_DRAIN",
	"BBR_STATE_PROBE_BW",
	"BBR_STATE_PROBE_RTT",
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
	"To long in startup", /* 10 */
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

static uint32_t prev_bwsamp_lost = 0;
static uint32_t prev_bwsamp_del = 0;


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


static void inline
print_out_space(FILE *outp)
{
	fprintf(outp, "                                   ");
}

static void
print_sack_blocks(struct tcpopt *to, uint32_t th_ack)
{
	int i, num_sack_blks=0;
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
	if (dump_out_sack) {
		print_out_space(out);
		fprintf(dump_out_sack, "ACK:%u\n", th_ack);
	}
	print_out_space(out);
	if (SEQ_LT(sack_blocks[0].start, th_ack))
		fprintf(out, "ACK:%u\n", th_ack);
	else
		fprintf(out, "ACK:%u (missing %u)\n", th_ack, (sack_blocks[0].start - th_ack));
	for(i=0; i<num_sack_blks; i++) {
		print_out_space(out);
		if (SEQ_LT(sack_blocks[i].start, th_ack))
			fprintf(out, "D-SACK:%u:%u\n",
				sack_blocks[i].start,
				sack_blocks[i].end);
		else
			fprintf(out, "SACK:%u:%u\n",
				sack_blocks[i].start,
				sack_blocks[i].end);
		if (dump_out_sack) {
			print_out_space(out);
			fprintf(dump_out_sack, "SACK:%u:%u\n", 
				sack_blocks[i].start,
				sack_blocks[i].end);
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

static void
display_tcp_option(const struct tcp_log_buffer *l)
{
	fprintf(out, "Option:%u Value:%u\n",
		l->tlb_flex1,
		l->tlb_flex2);
}


static int include_user_send = 0;
static char foobar100[32];

static const char *
get_jr_reason(uint32_t reas)
{
	if (reas == BBR_JR_SENT_DATA)
		return ("Done Sending");
	if (reas == BBR_JR_CWND_LIMITED)
		return ("CWND Limited");
	if (reas == BBR_JR_RWND_LIMITED)
		return ("RWND Limited");
	if (reas == BBR_JR_APP_LIMITED)
		return ("APP Limited");
	if (reas == BBR_JR_ASSESSING)
		return ("Assessing");
	sprintf(foobar100, "unknown:%d?",
		reas);
	return (foobar100);
}

#define SHRINKS_LAST 11
static const char *shrinks_reasons[] = {
	"RTTS Initial setting",
	"RTTS Measured new lower RTT",
	"RTTS Exiting ProbeRTT",
	"RTTS Was Idle",
	"RTTS Persits",
	"RTTS Reaches Target",
	"RTTS Adjusting ProbeRTT Interval",
	"RTTS Shrinks pg",
	"RTTS Shrinks pg final",
	"RTTS New Target",
	"RTTS declares victory",
	"RTTS Unknown"
};

static int show_record = 0;
static int ann_end = 0;

static void 
dump_log_entry(const struct tcp_log_buffer *l, const struct tcphdr *th)
{
	const char *mask;
	uint32_t delay, calc1, calc2;
	uint32_t time_display;
	int id, val;
	struct tcpopt to;
	char sign=0, foo;
	const struct tcp_log_bbr *bbr;
	uint32_t th_ack, th_seq, sub, dif;
	int colat;
	
	id = l->tlb_eventid;
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
	bbr = &l->tlb_stackinfo.u_bbr;
	if ((id != TCP_LOG_USERSEND) &&
	    (id != TCP_LOG_SOCKET_OPT)){
		if (first_time_set == 0) {
			last_evt_time = first_time = bbr->timeStamp;
			first_time_set = 1;
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
	if ((bbr->use_lt_bw) && (using_lt_bw == 0)) {
		time_started_using_ltbw = bbr->timeStamp;
		time_data_ltbw = bbr->timeStamp;
		if (time_ended_using_lt_bw) {
			delay =  bbr->timeStamp - time_ended_using_lt_bw;
		} else
			delay = 0;
		if (show_all_messages == 0) {
			fprintf(out, "# Started using LTBW\n");
		}
		using_lt_bw = 1;
	} else if ((using_lt_bw) && (bbr->use_lt_bw == 0)) {
		if (SEQ_GT(bbr->timeStamp, time_started_using_ltbw)) {
			total_time_using_lt_bw += (bbr->timeStamp - time_started_using_ltbw);
			time_started_using_ltbw = bbr->timeStamp;
			time_ended_using_lt_bw =  bbr->timeStamp;
		}
		if (show_all_messages == 0) {
			fprintf(out, "# Stopped using LTBW\n");
		}
		using_lt_bw = 0;
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
	tlb_sn = l->tlb_sn;
	if (show_all_messages) {
		if ((id != TCP_LOG_USERSEND) &&
		    (id != TCP_LOG_SOCKET_OPT)){
			if (time_is_relative && first_time_set) {
				time_display = bbr->timeStamp - first_time;
			} else {
				time_display = bbr->timeStamp;
			}
		} else {
			time_display = 0;
		}
		if (id == BBR_LOG_STATE) {
			if ((log_all_state_change == 0) && (bbr->bbr_state == 3) && (opg == bbr->hptsi_gain) && (bbr->bbr_state == old_state))
				;
			else {
				fprintf(out,
					"%u %u [%c%u] %s **********************************************************************************\n",
					time_display, number_flow, sign, dif, evt_name(id));
				if (show_record)
					fprintf(out, "|%u|%u %u [%c%u] %s ",
						l->tlb_sn, time_display, number_flow, sign, dif, evt_name(id));
				else
					fprintf(out, "%u %u [%c%u] %s ", time_display, number_flow, sign, dif, evt_name(id));
			}
		} else {
			if ((id != TCP_LOG_USERSEND) &&
			    (id != TCP_LOG_SOCKET_OPT)) {
				if (show_record)
					fprintf(out, "|%u|%u %u [%c%u] %s ",
						l->tlb_sn, time_display, number_flow, sign, dif, evt_name(id));
				else
					fprintf(out, "%u %u [%c%u] %s ",  time_display, number_flow, sign, dif, evt_name(id));
			} else
				fprintf(out, "%s ", evt_name(id));
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
		uint32_t tim_dif, sec, usec;
		const char *reas;
		
		tim_dif = bbr->flex3 - bbr->flex2;
		sec = tim_dif / 1000000;
		usec = tim_dif - (sec * 1000000);
		if (bbr->flex8 < SHRINKS_LAST)
			reas = shrinks_reasons[bbr->flex8];
		else
			reas = shrinks_reasons[SHRINKS_LAST];
		if (bbr->flex8 == 6) {
			fprintf(out, " %s(%u) was:%u applied:%u new-int:%u (Time Since %d.%d) tar:%u flt:%u\n",
				reas,
				bbr->flex1, bbr->flex2, bbr->flex3, bbr->flex4, sec, usec,
				bbr->flex6, bbr->inflight);

		} else {
			fprintf(out, " %s(%u) was:%u applied:%u at:%u (Time Since %d.%d) tar:%u flt:%u pg:%d\n",
				reas,
				bbr->flex1, bbr->flex2, bbr->flex3, bbr->flex4, sec, usec,
				bbr->flex6, bbr->inflight, bbr->hptsi_gain);
		}
	}
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
			const char *tstr;
			uint64_t calc;
			uint32_t tim_lt, los_per_lt=0;
			uint32_t tim_gt,los_per_gt=0;
			int printed=0;
			char prin_buf[100];
			
			/* Set in times */
			prin_buf[0] = 0;
			tim_gt = bbr->flex4;
			tim_lt = bbr->applimited;
			/* Set in gt */
			if ((bbr->pkts_out + bbr->flex3) > 0) {
				calc = bbr->pkts_out;
				calc *= 10000;
				calc /= (bbr->pkts_out + bbr->flex3);
				los_per_gt = calc;
			}
			/* set in lt */
			if ((bbr->lost + bbr->lt_epoch) > 0) {
				calc = bbr->lost;
				calc *= 10000;
				calc /= (bbr->lost + bbr->lt_epoch);
				los_per_lt = calc;
			}
			if (bbr->flex7 == 1)
				tstr = "Reduce greater";
			else if (bbr->flex7 == 2)
				tstr = "Increase greater";
			else if (bbr->flex7 == 3)
				tstr = "Skip greater";
			else if (bbr->flex7 == 4) {
				tstr = "Lesser to hot greater";
				if (lesser_is_hot == 0) {
					lesser_goes_hot = bbr->timeStamp;
					lesser_is_hot = 1;
				}
			} else if (bbr->flex7 == 5) {
				tstr = "Lesser no longer hot greater";
				if (lesser_is_hot) {
					time_in_hot += (bbr->timeStamp - lesser_goes_hot);
					lesser_is_hot = 0;
					sprintf(prin_buf, " hot for:%u", (bbr->timeStamp - lesser_goes_hot));
				}
			} else if (bbr->flex7 == 6) {
				double per;

				per = los_per_lt * 1.0;
				per /= 100;
				fprintf(out, "Loss percentage for lowgain is %3.2f%%\n",
					per);
				printed = 1;
			} else if (bbr->flex7 == 7) {
				tstr = "rst greater line";
			} else
				tstr = "Unknown";
			if (printed == 0)
				fprintf(out, "%s:%u lesser:%u new_lowgain:%u cruise_cnt:%u pe:%u hot:%d %s [lt:%u_%u gt:%u_%d]\n",
					tstr,
					bbr->flex1, bbr->flex2,
					bbr->flex6,
					bbr->flex5, bbr->pkt_epoch,
					bbr->flex8, prin_buf,
					los_per_lt, tim_lt,
					los_per_gt, tim_gt);

		}
		break;
	case TCP_LOG_RTT:
		fprintf(out, " rtt:%u applied to srtt\n",
			bbr->flex1);
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
			fprintf(out, " act:%d on_min_sleep:%u nxt_slot:%u cur_slot:%u reqslot:%u paceslot:%u\n",
				bbr->flex7,
				bbr->flex8,
				bbr->flex1,
				bbr->flex2,
				bbr->flex3,
				bbr->flex4);
			if (extra_print) {
				print_out_space(out);
				fprintf(out, "slotnow:%u newto:%u haveslept:%u yet:%u cr_ret:%d sleep_time:%u\n",
					bbr->flex5,
					bbr->flex6,
					bbr->epoch,
					bbr->lt_epoch,
					(int)bbr->pkts_out, bbr->applimited);
			}
		}
		break;
	case BBR_LOG_BBRTSO:
		if (show_all_messages) {
			fprintf(out, " TSO size:%u adjust:%u min_pacer_sleep:%u min_pace_sz:%d old:%u\n",
				bbr->flex1, bbr->flex2, bbr->flex3, bbr->flex4, bbr->flex5);
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
			const char *reas_name=NULL, *stage;
			
			if (bbr->flex8 == 0) {
				stage = "GAIN";
				if (bbr->flex7 == 1) {
					reas_name = "hit probe-rtt ";
				} else if (bbr->inflight > bbr->flex1) {
					reas_name = "hit target ";
				} else if ((l->tlb_snd_max - l->tlb_snd_una) >= l->tlb_snd_wnd) {
					reas_name = "rwnd limit";
				} else {
					reas_name = "unknown ";
				}
			} else if (bbr->flex8 == 1) {
				stage = "DRAIN";
				reas_name= "hit target";
			} else {
				stage = "LEVEL";
				reas_name = "none";
			}
			fprintf(out, " %s DR:%s pg:%d target:%u flight:%u lost:%u tso:%u flags:0x%x pe:%u\n",
				stage,
				display_bw(bbr->delRate, 0),
				bbr->hptsi_gain,
				bbr->flex1,
				bbr->inflight,
				bbr->lost,
				bbr->flex4, bbr->flex3, bbr->pkt_epoch);
			if (extra_print) {
				print_out_space(out);
				fprintf(out, "saved_nxt_epoch:%d epoch:%d rw:%u %s\n",
					bbr->flex6,
					bbr->epoch, l->tlb_snd_wnd, reas_name);
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
		fprintf(out, "bw:%s(%lu) len:%u gain:%u -> usecs:%u (used %s:%lu ohr:0x%x)\n",
			display_bw(bbr->delRate, 0), bbr->delRate,
			bbr->flex2,
			bbr->flex7,
			bbr->flex1, ((bws == NULL) ? "0.0" : bws), a, bbr->flex5);
		if (bws)
			free(bws);
		if (extra_print) {
			/* Assume hz = 1000 */
			print_out_space(out);
			fprintf(out, "tv %lu.%6.6lu ticks:%u cts:%u cw:%u over:%u srtt:%u\n",
				l->tlb_tv.tv_sec, l->tlb_tv.tv_usec, l->tlb_ticks, bbr->timeStamp, l->tlb_snd_cwnd,
				bbr->flex6, ((l->tlb_srtt*1000) >> TCP_RTT_SHIFT));
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
	case BBR_LOG_DOSEG_DONE:
		if (show_all_messages) {
			char *bw_str;
			
			bw_str = display_bw(bbr->delRate, 1);
			if (bbr->flex4)
				mask = get_timer_mask(bbr->flex4);
			else
				mask = "NONE";
			fprintf(out, "DR:%s cDR:%s do:%d np:%d wo:%d in_per:%d (ip:%d pe:%d) tmrs:%s exp:%u cw:%u\n",
				bw_str,
				display_bw(bbr->cur_del_rate, 0),
				bbr->flex1,
				bbr->flex2,
				bbr->flex7,
				bbr->flex8, bbr->inhpts, bbr->pkt_epoch,
				mask, bbr->flex5, l->tlb_snd_cwnd);
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
			fprintf(out, " e:%u pe:%u del:%u lost:%u (%lu) from line:%d epoch_rtt:%u DR:%s cDR:%s mc:%u [%c%3.2f%%]\n",
				bbr->epoch,
				bbr->pkt_epoch,
				bbr->flex2,
				bbr->flex1,
				mul,
				bbr->flex7,
				(bbr->timeStamp - prev_pkt_epoch), /* delta */
				dr, cdr, bbr->inflight,
				sign,
				perc);
			if (extra_print) {
				print_out_space(out);
				fprintf(out, "btlbw:%lu\n",
					bbr->delRate);
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
	case TCP_LOG_IN:
	{
		int off_len;
		uint32_t tasf;
		const char *ackflags;
		if (th) {
			ackflags = translate_flags(th->th_flags);
			th_ack = ntohl(th->th_ack);
			th_seq = ntohl(th->th_seq);
			off_len = th->th_off << 2;
			tasf = th_ack - l->tlb_iss;
		} else {
			ackflags = "UNK";
			off_len = 0;
			th_ack = 0xbadbad;
			th_seq = 0xbadbad;
			tasf = 0;
		}
		sub = bbr->timeStamp - last_ack_time;
		last_ack_time = bbr->timeStamp;
		if (show_all_messages) {
			const uint8_t *optptr;
			fprintf(out, "Acks %u (%s) [Nsegs:%d] off:%d out:%u len_in:%u avail:%u cw:%u rw:%u ts:%d (spa:%u ip:%d ii:%d)\n",
				(th_ack - l->tlb_snd_una),
				ackflags,
				bbr->flex1,
				off_len,
				(l->tlb_snd_max - l->tlb_snd_una),
				l->tlb_len,
				l->tlb_txbuf.tls_sb_acc,
				l->tlb_snd_cwnd,
				l->tlb_snd_wnd,
				l->tlb_state, 
				sub, bbr->inhpts, bbr->ininput);
			if (extra_print) {
				print_out_space(out);
				fprintf(out, " snd_una:%u th_ack:%u pe:%u th_seq:%u rcv_nxt:%u tasf:%u\n",
					l->tlb_snd_una, th_ack, bbr->pkt_epoch, th_seq, l->tlb_rcv_nxt, tasf);
				optptr = (const uint8_t *)th;
				optptr += sizeof(struct tcphdr);
				process_options(&to, th, optptr);
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
			"%s pe:%u sec:%u lse:%u lost_as:%u (lost tot:%u) gain req:%u oldbttlbw:%lu Dr:%lu\n",
			pstr,
			bbr->pkt_epoch,
			bbr->flex4,
			bbr->flex1,
			bbr->flex2,
			bbr->lost,
			bbr->flex3, bbr->cur_del_rate, bbr->delRate);
	}
	break;
	case TCP_LOG_OUT:
	{
		const char *bwd;
		int sidx;
		int rec, drain, hot, ured;
		int bw_override = 0;
		uint64_t bwo;
		
		ured = bbr->flex2 & 0x1;
		hot = (bbr->flex2 >> 1) & 0x1;
		drain = (bbr->flex2 >> 2) & 0x1;
		rec = (bbr->flex2 >> 3) & 1;
		if (bbr->bbr_state == BBR_STATE_PROBE_RTT)
			bw_override = 1;
		 else if ((bbr->bbr_state == BBR_STATE_PROBE_BW) &&
			((bbr->bbr_substate == BBR_SUB_GAIN) ||
			 (bbr->bbr_substate == BBR_SUB_DRAIN)))
			bw_override = 1;
		if (rec) {
			bwd = display_bw(bbr->bw_inuse, 0);
			bwo = bbr->bw_inuse;
		} else if ((bw_override == 0) && (hot || rec || ured)) {
			bwd = display_bw(bbr->bw_inuse, 0);
			bwo = bbr->bw_inuse;
		} else {
			bwd = display_bw(bbr->delRate, 0);
			bwo = bbr->delRate;
		}
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
		if (bbr->flex8 == 1){
			retran_count += l->tlb_len;
			foo = '*';
		} else {
			foo = ' ';
		}
		state_send_count++;
		state_send_bytes += l->tlb_len;
		sub = bbr->timeStamp - last_out_time;
		last_out_time = bbr->timeStamp;
		if (show_all_messages) {
			fprintf(out, "Sent(e:%d) %u:%u%c (%s:%d) flight:%u avail:%d (spo:%u ip:%d ii:%d rdhu:0x%x %s(%lu) pg:%u)\n",
				l->tlb_errno,
				th_seq, l->tlb_len, foo,
				translate_flags(th->th_flags), l->tlb_errno,
				bbr->inflight,
				l->tlb_txbuf.tls_sb_acc,
				sub, bbr->inhpts, bbr->ininput,
				bbr->flex2, bwd, bwo, bbr->hptsi_gain);
			if (extra_print) {
				uint32_t low, high;

				print_out_space(out);
				fprintf(out, "cw:%u rw:%u pe:%u delay:%u tso:%u agg_delay:%u maxseg:%u output_from:%u\n",
					l->tlb_snd_cwnd,
					l->tlb_snd_wnd,
					bbr->epoch,
					bbr->flex4, 
					bbr->flex6, bbr->flex1,
					bbr->flex3, bbr->flex5);
				print_out_space(out);
				low = bbr->rttProp & 0x00000000ffffffff;
				high = (bbr->rttProp >> 32);
				fprintf(out, "tv %lu.%6.6lu ticks:%u cts:%u l:%u h:%u (%u)\n",
					l->tlb_tv.tv_sec, l->tlb_tv.tv_usec, l->tlb_ticks,
					bbr->timeStamp, low, high, (high - low));
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
	case TCP_LOG_TF_ACK:
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
			 * bbr_log_type_bbrupd(struct tcp_bbr *bbr, uint8_t arg2, uint32_t arg3-cts,
			 *                     uint32_t arg4, uint32_t arg5, uint32_t arg6,
			 *		       uint32_t arg7, uint32_t arg8, int arg9, uint32_t arg10)
			 * log.u_bbr.flex1 = 0;
			 * log.u_bbr.flex2 = arg5;
			 * log.u_bbr.flex3 = arg4;
			 * log.u_bbr.flex4 = arg10;
			 * log.u_bbr.flex5 = arg6;
			 * log.u_bbr.flex6 = arg7;
			 * log.u_bbr.flex7 = arg9;

			 * log.u_bbr.flex8 = arg2
			 * log.u_bbr.pkts_out = arg8;
			 * len = rsmsend;
			 * if ((app == 12) && bbr->rc_reduce_bw) {
			 *     log.u_bbr.delRate = bbr->r_ctl.red_bw;
			 * log.u_bbr.flex8 = appl;
			 * log.u_bbr.applimited = bbr->r_rate_open;
			 */
			cur_del_rate_str = display_bw(bbr->cur_del_rate, 1);
			if (bbr->flex8 == 10) {
				fprintf(out, "App:%d idx:%d DR:%s cDR:%s lt:%lu del:%u tim:%u  pe:%d grad:%u\n",
					bbr->flex8,
					bbr->flex7,
					bw_str,
					cur_del_rate_str,
					bbr->bw_inuse,
					bbr->flex2, bbr->flex3,
					bbr->pkt_epoch,
					bbr->flex5);
				if (extra_print) {
					print_out_space(out);					
					fprintf(out, " BBRUPD avail:%u flight:%d  fs_2_fa:%u ls_2_la:%u mwnd:%u pg:%d cg:%d\n",
						l->tlb_txbuf.tls_sb_acc, bbr->inflight, 
						bbr->flex6, bbr->pkts_out, bbr->flex4,
						bbr->hptsi_gain, bbr->cwnd_gain);
				}
			} else if (bbr->flex8 == 5) {
				fprintf(out, "App:%d idx:%d rs:%u re:%u (%u) mss:%u ro:0x%x\n",
 					bbr->flex8, /* app */
					bbr->flex7, /* index */
					bbr->flex2, /* rt_start */
					bbr->flex5, /* rt_end */
					(bbr->flex5 - bbr->flex2),
					bbr->flex6, /* maxseg */
					bbr->flex4); /* rt_open */
			} else if ((bbr->flex8 == 6) || (bbr->flex8 == 7)) {
				uint64_t tbw;

				tbw = bbr->flex5;
				tbw <<= 32;
				tbw |= bbr->flex6;
				fprintf(out, "App:%d idx:%d del:%u tim:%u rtlen:%u lrtt:%u  alt-bw:%s cDR:%s\n",
 					bbr->flex8, /* app */
					bbr->flex7, /* index */
					bbr->flex2, /* delivered */
					bbr->flex3, /* tim */
					bbr->flex4, /* r_seq_end - r_seq_start */
					bbr->pkts_out, /* lrtt */
					display_bw(tbw, 0), cur_del_rate_str);
			} else if (bbr->flex8 == 9) {
				const char *fooee;
				if (bbr->flex5 == 0)
					fooee = ((bbr->flex6 > bbr->pkts_out) ? "+" : "-");
				else
					fooee = "=";
				fprintf(out, "App:%d idx:%d DR:%s cDR:%s lt:%lu del:%u tim:%u pe:%d f_rtt:%u l_rtt:%u (%s)\n",
					bbr->flex8,
					bbr->flex7,
					bw_str,
					cur_del_rate_str,
					bbr->bw_inuse,
					bbr->flex2, bbr->flex3,
					bbr->pkt_epoch,
					bbr->flex6,
					bbr->pkts_out,
					fooee
					);
			} else if (bbr->flex8 == 11) {
				fprintf(out, "App:%d DR:%s avail:%u flight:%d pe:%d Open-expand idx:%d seqstart:%u rs:%u re:%u hr:%d%d\n",
					bbr->flex8,
					bw_str,
					l->tlb_txbuf.tls_sb_acc, bbr->inflight, bbr->pkt_epoch,
					bbr->flex7,
					bbr->flex2, bbr->flex3, bbr->flex5,
					bbr->flex6, bbr->pkts_out);
			} else if (bbr->flex8 == 12) {
				fprintf(out, "App:%d DR:%s avail:%u flight:%d pe:%d Capped idx:%d rs:%u re:%u (%u) hr:%d%d\n",
					bbr->flex8,
					bw_str,
					l->tlb_txbuf.tls_sb_acc,
					bbr->inflight, bbr->pkt_epoch,
					bbr->flex7,
					bbr->flex2, bbr->flex5,
					(bbr->flex5 - bbr->flex2),
					bbr->flex4, bbr->flex6);
			} else if ((bbr->flex8 == 17) || (bbr->flex8 == 18)) {
				fprintf(out, "App:%d avail:%u flight:%d pe:%d Abanondoned idx:%d seqs:%u ends:%u (%d) hot:%d red:%d\n",
					bbr->flex8,
					l->tlb_txbuf.tls_sb_acc, bbr->inflight, bbr->pkt_epoch,
					bbr->flex7,
					bbr->flex2, bbr->flex5, ((int32_t)bbr->flex5 - (int32_t)bbr->flex2), bbr->flex6, bbr->pkts_out);
			} else {
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
			if (extra_print) {
				print_out_space(out);
				if (bbr->applimited == 0x1f)
					fprintf(out, "BBRUPD rate_open:None\n");
				else
					fprintf(out, "BBRUPD rate_open:%d\n", bbr->applimited);
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
			}
		}
		break;
	case BBR_LOG_ACKCLEAR:
		if (show_all_messages)
			fprintf(out, "Avail:%u cw:%u rw:%u (ip:%d ii:%d ult:%d) rttProp:%ld %u\n",
				l->tlb_txbuf.tls_sb_acc,
				l->tlb_snd_cwnd,
				l->tlb_snd_wnd,
				bbr->inhpts, bbr->ininput, bbr->use_lt_bw, bbr->rttProp, bbr->pkt_epoch);
		if (dump_out_sack) {
			fprintf(dump_out_sack, "EXIT\n");
		}
		break;
	case BBR_LOG_INQUEUE:
		assert(bbr->bbr_state < 5);
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
			fprintf(out, "type:%s(%s) lineno:%d for %u(%u)  cw:%u pg:%d cg:%d pe:%u del:%u lost:%u\n",
				mask,
				which_one,
				bbr->flex1,
				bbr->flex2, bbr->flex4, l->tlb_snd_cwnd, bbr->hptsi_gain, bbr->cwnd_gain,
				bbr->pkt_epoch, bbr->delivered, bbr->lost);
			if (extra_print) {
				uint32_t calc_trxt;

				print_out_space(out);
				fprintf(out, "srtt:%u rttvar:%u rtt_shift:%d\n", l->tlb_srtt, l->tlb_rttvar, TCP_RTT_SHIFT); 
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
			fprintf(out, "type:%s lineno:%d for %u usecs cw:%u e:%u pe:%u bbr_state:%d-%d\n",
				mask,
				bbr->flex1,
				bbr->flex2, l->tlb_snd_cwnd, bbr->epoch, bbr->pkt_epoch,
				bbr->bbr_state, bbr->bbr_substate);
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
			fprintf(out, "cw:%u ocw:%u rw:%u seq:%u flags:0x%x snduna:%u sndmax:%u cDR:%s flight:%u\n",
				l->tlb_snd_cwnd,
				bbr->flex2,
				l->tlb_snd_wnd,
				bbr->flex1,
				l->tlb_flags,
				l->tlb_snd_una,
				l->tlb_snd_max,
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
			fprintf(out, "held-cw:%u re:%u e:%u flags:0x%x out:%u cw:%u rw:%u snduna:%u sndmax:%u pe:%u\n",
				bbr->flex2,
				bbr->flex1,
				bbr->epoch,
				l->tlb_flags,
				(l->tlb_snd_max - l->tlb_snd_una),
				l->tlb_snd_cwnd,
				l->tlb_snd_wnd,
				l->tlb_snd_una,
				l->tlb_snd_max, bbr->pkt_epoch);
		break;
	case BBR_LOG_CWND:
		if (show_all_messages) {
			if (bbr->flex8 != 44) {
				fprintf(out, "cw:%u bta:%u sack-chg:%u prev_ack:%u meth:%d line:%d tcw:%u cwg:%u\n",
					l->tlb_snd_cwnd,
					bbr->flex3,
					bbr->flex4,
					bbr->flex2,
					bbr->flex8,
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
				fprintf(out, "line:%u low_rtt:%u high_rtt:%u h-l-d:%u cwnd_raw:%u target:%u\n",
					bbr->flex1,
					bbr->flex2,
					bbr->flex3,
					bbr->flex4,
					bbr->flex5,
					bbr->flex6);
			}
		}
		if (dump_out_sack && bbr->flex4) {
			fprintf(dump_out_sack, "CHG:%u\n", bbr->flex4);
		}
		break;
	case BBR_LOG_BWSAMP:
	{
		uint32_t del_to, lost_to;
		double top, bot, perc;

		val = bbr->flex1;
		if (val >= REASON_MAX) {
			val = REASON_MAX-1;
		}
		lost_to = bbr->lost - prev_bwsamp_lost;
		del_to = bbr->delivered - prev_bwsamp_del;
		if (prev_bwsamp_del) {
			if (SEQ_LT(prev_bwsamp_del,bbr->delivered)) {
				top = lost_to * 100.0;
				bot = del_to * 1.0;
				perc = top / bot;
			} else {
				perc = 100.0;
			}
		} else {
			perc = 0.0;
		}
		if (show_all_messages)
			fprintf(out, "%s lt_bw:%lu DR:%s lt_e:%u lost:%u del:%u e:%u pe:%u alu:%u (l2:%u d2:%u loss-per:%2.3f)\n",
				lt_bw_reasons[val],
				bbr->bw_inuse,
				display_bw(bbr->delRate, 0),
				bbr->lt_epoch,
				bbr->lost,
				bbr->delivered,
				bbr->epoch,
				bbr->pkt_epoch,
				bbr->applimited,
				lost_to, del_to, perc);
		prev_bwsamp_lost = bbr->lost;
		prev_bwsamp_del = bbr->delivered;
	}
	break;
	case BBR_LOG_MSGSIZE:
		fprintf(out, "\n");
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
		assert(bbr->bbr_state < 5);
		if ((show_all_messages == 1) && (log_all_state_change == 0) && (bbr->bbr_state == 3) && (opg == bbr->hptsi_gain) && (bbr->bbr_state == old_state)) {
			break;
		}
		calc1 = bbr->delivered - del_at_state;
		calc2 = bbr->lost - lost_at_state;
		if (show_all_messages) {
			uint32_t gain;

			gain = bbr->cwnd_gain;
			fprintf(out, "bbrstate:%s:[%d] opg:%d -> pg:%d stayed:%u usecs DR:%s rttProp:%ld flight:%u tcw:%u srtt:%u\n",
				major_state[bbr->bbr_state],
				bbr->bbr_substate,
				opg, bbr->hptsi_gain,
				(bbr->timeStamp - last_pg_chg),
				display_bw(bbr->delRate,0),
				bbr->rttProp,
				bbr->inflight,
				bbr->pkts_out, ((l->tlb_srtt*1000) >> TCP_RTT_SHIFT));
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
				fprintf(out, "rtt_probe_lim:%u das:%u las:%u ssc:%u ssb:%u prttl:%u ult:%d lse:%u lsl:%u exdel:%u\n",
					bbr->flex3,
					calc1, calc2, state_send_count, state_send_bytes,  bbr->flex4, bbr->use_lt_bw,
					bbr->flex5, bbr->flex6, bbr->flex7 );
			}
			fprintf(out,
				"%u %u [%c%u] %s **********************************************************************************\n",
				time_display, number_flow, sign, dif, evt_name(id));
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
		state_send_count = 0;
		max_rtt_in_state = 0;
		min_rtt_in_state = 0xffffffff;
		state_send_bytes = 0;
		del_at_state = bbr->delivered;;
		lost_at_state = bbr->lost;
		opg = bbr->hptsi_gain;
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

static void 
dump_rack_log_entry(const struct tcp_log_buffer *l, const struct tcphdr *th)
{
	const struct tcp_log_bbr *bbr;
	uint32_t th_ack, th_seq, timeoff, calc, time_display;
	int id, val;
	char *mask;
	struct tcpopt to;
	
	if (l->tlb_eventid == TCP_LOG_RTO) {
		tlb_sn = l->tlb_sn;
		return;
	}
	bbr = &l->tlb_stackinfo.u_bbr;
	id = l->tlb_eventid;
	if (first_time_set == 0) {
		first_time = l->tlb_ticks;
		first_time_set = 1;
	}
	if (prev_tick == 0) {
		prev_tick_set = l->tlb_ticks;
		prev_tick = 1;
	}
	if (time_is_relative && first_time_set) {
		time_display = l->tlb_ticks - first_time;
	} else {
		time_display = l->tlb_ticks;
	}
	timeoff = l->tlb_ticks - prev_tick;
	prev_tick = l->tlb_ticks;
	if (show_record) 
		fprintf(out, "|%u|%u %u rack [%u] %s ",
			l->tlb_sn, time_display, number_flow, timeoff, evt_name(id));
	else
		fprintf(out, "%u %u rack [%u] %s ",  time_display, number_flow, timeoff, evt_name(id));
	switch (id) {
	default:
	case TCP_LOG_TF_ACK:
	case TCP_LOG_BAD_RETRAN:
	case TCP_LOG_PRR:
	case TCP_LOG_REORDER:
	case TCP_LOG_HPTS:
	case BBR_LOG_EXIT_GAIN:
	case BBR_LOG_PERSIST:
	case BBR_LOG_PKT_EPOCH:
	case BBR_LOG_BBRUPD:
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
	case BBR_LOG_DOSEG_DONE:
		mask = get_timer_mask(bbr->flex4);
		fprintf(out, "do:%d np:%d wo:%d in_per:%d (ip:%d) tmrs:%s exp:%u way_out:%d out:%u state:%u\n",
			bbr->flex1,
			bbr->flex2,
			bbr->flex7,
			bbr->flex8,
			bbr->inhpts, 
			mask, bbr->flex5,
			bbr->flex3,
			(l->tlb_snd_max - l->tlb_snd_una), l->tlb_state);
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
		fprintf(out, " rtt:%u applied to srtt state:%u\n",
			bbr->flex1, l->tlb_state);
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
			fprintf(out, "type:%s(%s:%x) srtt:%d for %u(%u) cw:%u rw:%u (ip:%d iip:%d) rc:%d minto:%d t_rxtcur:%u state:%u\n",
				mask,
				which_one, bbr->flex3,
				bbr->flex1,
				bbr->flex2, bbr->flex4,
				l->tlb_snd_cwnd, l->tlb_snd_wnd,
				bbr->inhpts, bbr->ininput,
				bbr->flex4, bbr->flex5, bbr->flex6, l->tlb_state);
		}
		break;
	case BBR_LOG_TIMERCANC:
		mask = get_timer_mask(bbr->flex3);
		if (show_all_messages)
			fprintf(out, "type:%s cw:%u rw:%u tp_flags:0x%x (ip:%d iip:%d) rm_frm_pacer:%d state:%u line:$%d\n",
				mask,
				l->tlb_snd_cwnd, l->tlb_snd_wnd,
				l->tlb_flags,
				bbr->inhpts, bbr->ininput,
				bbr->flex8, l->tlb_state,
				bbr->flex1
				);

		break;
	case BBR_LOG_TO_PROCESS:
		if (show_all_messages) {
			int32_t ret;

			ret = (int32_t)bbr->flex2;
			if (ret >= 0) {
				mask = get_timer_mask(bbr->flex1);
				fprintf(out, " timers %s return %d expires:%u state:%u\n",
					mask, bbr->flex2, bbr->flex3, l->tlb_state);
			} else {
				/* A early to */
				mask = get_timer_mask(bbr->flex4);
				if (ret == -1) {
					fprintf(out, "Output in progress tmr %s state:%u flags:%x\n",
						mask, l->tlb_state, l->tlb_flags);
				} else if (ret == -2) {
					fprintf(out, "Not pacer calling for tmr %s state:%u\n",
						mask, l->tlb_state);
				} else {
					fprintf(out, "Not enough time yet tmr %s left:%d reinsert cts:%u exp:%u state:%u\n",
						mask, bbr->flex1, bbr->flex5, bbr->flex3, l->tlb_state);
				}
			}
		}
		break;
	case BBR_LOG_BBRSND:
		fprintf(out, "slot:%u (ip:%d ii:%d) state:%u\n",
			bbr->flex1, bbr->inhpts, bbr->ininput, l->tlb_state);
		break;
	case BBR_LOG_JUSTRET:
		fprintf(out, "slot:%u (ip:%d ii:%d pc:%d) in_persist:%d avail:%u rw:%u out:%u state:%u\n",
			bbr->flex1, bbr->inhpts, bbr->ininput,
			bbr->flex7, bbr->flex8,
			l->tlb_txbuf.tls_sb_acc,
			l->tlb_snd_wnd, (l->tlb_snd_max - l->tlb_snd_una), l->tlb_state);
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

	case TCP_LOG_IN:
	{
		int off_len;
		const uint8_t *optptr;
		if (th) {

			th_ack = ntohl(th->th_ack);
			th_seq = ntohl(th->th_seq);
			off_len = th->th_off << 2;
		} else {
			off_len = 0;
			th_ack = 0xbadbad;
			th_seq = 0xbadbad;
		}
		fprintf(out, "Acks %u (%s) off:%u out:%u lenin:%u avail:%u cw:%u rw:%u una:%u ack:%u (spa:%u ip:%d) state:%d t_flags:%x\n",
			(th_ack - l->tlb_snd_una),
			translate_flags(th->th_flags),
			off_len,
			(l->tlb_snd_max - l->tlb_snd_una),
			l->tlb_len,
			l->tlb_txbuf.tls_sb_acc,
			l->tlb_snd_cwnd,
			l->tlb_snd_wnd,
			l->tlb_snd_una,
			th_ack,
			(l->tlb_ticks - rack_last_in),
			bbr->inhpts, l->tlb_state, l->tlb_flags);
		rack_last_in = l->tlb_ticks;
		optptr = (const uint8_t *)th;
		optptr += sizeof(struct tcphdr);
		process_options(&to, th, optptr);
		if (to.to_flags & TOF_SACK) {
			print_sack_blocks(&to, th_ack);
		}
		if (th && (th->th_flags & TH_RST) && (ann_end == 0)) {
			ann_end = 1;
			fprintf(out, "***Flow Ends sent %u bytes\n", (l->tlb_snd_max - l->tlb_iss));
		}
		break;
	}
	case TCP_LOG_OUT:
	{
		const char *rtr;
		if (th) {
			th_ack = ntohl(th->th_ack);
			th_seq = ntohl(th->th_seq);
		} else {
			th_ack = 0xbadbad;
			th_seq = 0xbadbad;
		}
		rtr = " ";
		if (bbr->flex8) {
			rtr = "*";
		}
		if ((th_seq == l->tlb_snd_max) && (l->tlb_len == 0))
			rtr = " [Ack]";
		fprintf(out, "Sent(%d) %u:%u%s (%s) th_ack:%u out:%u avail:%d cw:%u rw:%u sst:%u state:%u srtt:%u (spo:%u ip:%d)\n",
			l->tlb_errno,
			th_seq, l->tlb_len, rtr, 
			translate_flags(th->th_flags),/* l->tlb_errno rack does not do this, */ th_ack,
			(l->tlb_snd_max - l->tlb_snd_una),
			l->tlb_txbuf.tls_sb_acc,
			l->tlb_snd_cwnd,
			l->tlb_snd_wnd, l->tlb_snd_ssthresh, l->tlb_state, (l->tlb_srtt >> TCP_RTT_SHIFT),
			(l->tlb_ticks - rack_last_out), bbr->inhpts );
		rack_last_out = l->tlb_ticks;
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
			fprintf(out, "Type:%s min_rtt:%u rack_rtt:%u out:%u cw:%u rw:%u t_flags:0x%x out:%d (ip:%d) state:%u\n",
				timer_types[val],
				bbr->flex1,
				bbr->flex2,
				(l->tlb_snd_max - l->tlb_snd_una),
				l->tlb_snd_cwnd,
				l->tlb_snd_wnd, l->tlb_flags,
				(l->tlb_snd_max - l->tlb_snd_una), bbr->inhpts, l->tlb_state);
		}
		break;
	case BBR_LOG_BBRRTT:
		fprintf(out, "rtt:%u o_srtt:%u o_var:%u srtt:%u var:%u avail:%u (ip:%d) state:%u\n",
			bbr->flex1,
			bbr->flex2,
			bbr->flex3,
			l->tlb_srtt,
			l->tlb_rttvar,
			l->tlb_txbuf.tls_sb_acc,
			bbr->inhpts, l->tlb_state
			);
		break;
	};
}

static int force_bbr=0;

static void 
dump_default_log_entry(const struct tcp_log_buffer *l, const struct tcphdr *th)
{
	uint32_t th_ack, th_seq, timeoff, calc;
	char *mask;
	int id;
	const struct tcp_log_bbr *bbr;
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
	id = l->tlb_eventid;
	if (prev_tick == 0) {
		prev_tick_set = l->tlb_ticks;
		prev_tick = 1;
	}
	timeoff = l->tlb_ticks - prev_tick;
	prev_tick = l->tlb_ticks;
	fprintf(out, "%u %u def [%u] %s ",  l->tlb_ticks, number_flow, timeoff, evt_name(id));
	switch (id) {
	default:


	case TCP_LOG_TF_ACK:
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
	case BBR_LOG_TIMERSTAR:
		if (show_all_messages) {
			const char *which_one;

			mask = get_timer_mask(bbr->flex3);
			if (bbr->flex8) {
				which_one = "pacer";				
			} else {
				which_one =  "timer";
			}
			fprintf(out, "type:%s(%s) srtt:%d for %u(%u) cw:%u rw:%u (ip:%d iip:%d) rc:%d minto:%d t_rxtcur:%u\n",
				mask,
				which_one,
				bbr->flex1,
				bbr->flex2, bbr->flex4,
				l->tlb_snd_cwnd, l->tlb_snd_wnd,
				bbr->inhpts, bbr->ininput,
				bbr->flex4, bbr->flex5, bbr->flex6);
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
		fprintf(out, " rtt:%u applied to srtt\n",
			bbr->flex1);
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

	case TCP_LOG_IN:
	{
		int off_len;
		const uint8_t *optptr;
		if (th) {

			th_ack = ntohl(th->th_ack);
			th_seq = ntohl(th->th_seq);
			off_len = th->th_off << 2;
		} else {
			off_len = 0;
			th_ack = 0xbadbad;
			th_seq = 0xbadbad;
		}
		fprintf(out, "Acks %u (%s) off:%u out:%u lenin:%u avail:%u cw:%u rw:%u una:%u ack:%u rto:%u srtt:%u state:%d\n",
			(th_ack - l->tlb_snd_una),
			translate_flags(th->th_flags),
			off_len,
			(l->tlb_snd_max - l->tlb_snd_una),
			l->tlb_len,
			l->tlb_txbuf.tls_sb_acc,
			l->tlb_snd_cwnd,
			l->tlb_snd_wnd,
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
	case TCP_LOG_OUT:
	{
		char rtr;
		const char *flags_out;
		if (th) {
			th_ack = ntohl(th->th_ack);
			th_seq = ntohl(th->th_seq);
			flags_out = translate_flags(th->th_flags);
		} else {
			th_ack = 0xbadbad;
			th_seq = 0xbadbad;
			flags_out = "no:th";
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
			fprintf(out, "Sent %u:%u%c (%s) th_ack:%u out:%u avail:%d cw:%u rw:%u ssthresh:%u state:%d\n",
				th_seq, l->tlb_len, rtr, 
				flags_out, th_ack,
				(l->tlb_snd_max - l->tlb_snd_una),
				l->tlb_txbuf.tls_sb_acc,
				l->tlb_snd_cwnd,
				l->tlb_snd_wnd, l->tlb_snd_ssthresh, l->tlb_state);
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

static void
read_pcap_records(const char *filein, int *c)
{
	const struct tcp_log_buffer *lbufp;
	const struct tcphdr *th;
	const char *stackname;
	void *ctx;
	int cnt, warnedstack;

	cnt = 0;
	ctx = bbr_init_file(filein, 1);
	if (ctx == NULL) {
		printf("Failed to init context with file %s\n",
		       filein);
		return;
	}
	th = NULL;
	if (display_file_names) {
		fprintf(out, "## FILE %s\n", filein);
	}
	warnedstack = -1;
	while(bbr_get_next(ctx, &lbufp, &th) == 0) {
		if (lbufp->tlb_stackid >= 10) {
			stack_cnts[9]++;
		} else {
			stack_cnts[lbufp->tlb_stackid]++;
		}
		stackname = bbr_get_stackname(ctx, lbufp->tlb_stackid);
		if (surpress && strcmp(stackname, surpress))
			continue;
		if (force_bbr || !strncmp(stackname, "bbr", 3)) {
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

int
main(int argc, char **argv)
{
	const char *filename=NULL;
	char file_construct[1024];
	double top, bot, perc;
	struct stat sbuf;
	int i, cnt=0;
	int notdone=1;
	int file_no=0;
	uint64_t actual_sending_time=0;
	uint64_t tot=0;
	int show_msg_stats=0;

	memset(msg_types_list, 0, sizeof(msg_types_list));
	memset(sent_state, 0, sizeof(sent_state));
	out = stdout;
	memset(stack_cnts, 0, sizeof(stack_cnts));
	while ((i = getopt(argc, argv, "RmD:Urtd:li:o:O?Ff:eN:w:s:")) != -1) {
		switch (i) {
		case 'R':
			show_record = 1;
			break;
		case 'm':
			show_msg_stats = 1;
			break;
		case 's':
			/* Surpress all but this guy */
			surpress = optarg;
			break;
		case 'w':
			warn_behind = strtoul(optarg, NULL, 0);;
			break;
		case 'N':
			number_flow = strtol(optarg, NULL, 0);
			break;
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
		case 'D':
			dump_out_sack = fopen(optarg, "w");
			if (dump_out_sack == NULL) {
				fprintf(stderr, "No sack information will be dumped can't open %s\n",
					optarg);
			}
		case 'U':
			include_user_send = 1;
			break;
		case 'F':
			display_file_names = 1;
			break;
		case 't':
			print_out_the_time = 1;
			break;
		case 'O':
			show_all_messages = 0;
			break;
		case 'r':
			time_is_relative = 1;
			break;
		case 'l':
			log_all_state_change = 0;
			break;
		case 'd':
			dirname = optarg;
			break;
		case 'o':
			out = fopen(optarg, "w");
			if (out == NULL) {
				fprintf(stderr, "Can't open %s for output err:%d\n",
					optarg, errno);
				exit(-1);
			}
			break;
	        case 'i':
			filename = optarg;
			break;
		case '?':
		default:
		use:
			fprintf(stderr, "%s -i sessionid  [-d dir -F -l -O -N -n -r -t -U -D sack-dump-file -e -w cnt -s statck]\n",
				argv[0]);
			fprintf(stderr, " -i sessionid - display the specified session\n");
			fprintf(stderr, " -d directory-where-files-are (default=/var/log/tcplog_dumps)\n");
			fprintf(stderr, " -F add file name in output\n");
			fprintf(stderr, " -l don't log all state transistions don't collapse the probe_bw neutral ones\n");
			fprintf(stderr, " -O condense message output showing minimal information\n");
			fprintf(stderr, " -r relative time on\n");
			fprintf(stderr, " -t print out the time too\n");
			fprintf(stderr, " -U include user send events in the display\n");
			fprintf(stderr, " -D file - specify a file to dump sack logging information to\n");
			fprintf(stderr, " -e - enable extra printing\n");
			fprintf(stderr, " -w behindcnt -- Warn to stderr if we get behind over behindcnt\n");
			fprintf(stderr, " -N num - place flow-num after the time (def=0)\n");
			fprintf(stderr, " -s stack - surpress the printing of all but this stacks info\n");
			exit(-1);
			break;
		};
	}
	if (filename == NULL)
		goto use;

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
	}
	fprintf(stderr, "Files:%d Processed %d records\n", file_no, cnt);
	for(i=0; i<10; i++) {
		if (stack_cnts[i]) {
			fprintf(stderr, "Saw %d records from stackid:%d total_missed:%ld dups:%u\n",
				stack_cnts[i], i, total_missed_records, duplicates);
		}
	}
	if (show_all_messages == 0) {
		fprintf(out, "# ");
	}
	if (extra_print) {
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
