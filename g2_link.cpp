
/*
 *   Copyright (C) 2010 by Scott Lawson KI4LKF
 *
 *   This program is free software; you can redistribute it and/or modify
 *   it under the terms of the GNU General Public License as published by
 *   the Free Software Foundation; either version 2 of the License, or
 *   (at your option) any later version.
 *
 *   This program is distributed in the hope that it will be useful, 
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the 
 *   GNU General Public License for more details.
 *
 *   You should have received a copy of the GNU General Public License 
 *   along with this program; if not, write to the Free Software
 *   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 */


/* by KI4LKF */


// Version History
//
// Version 4.00 - Ramesh Dhami, VA3UV - 2015.06.07
//                Ready for release
//
// Version 3.18 - Ramesh Dhami, VA3UV - 2015.06.07
//                Stripped out REF linking ability
//                Bug Fix to address issue where repeaters connecting to us directly were not showing the "source" in the log file and hence users
//                appearing on the dashboard were not showing the source - i.e., where are they coming from
//
// Version 3.17 - Ramesh Dhami, VA3UV - 2014.08.25
//                Bug fix - initialized temp_buff[] to clear out garbage
//
// Version 3.16 - Ramesh Dhami, VA3UV - 2014.07.09
//

// Version 3.14 - Ramesh Dhami, VA3UV - 2014.04.06
//                Added support for 3 separate LINK_AT_STARTUP hosts - 1 per RF module
//                RF_INACTIVITY_TIMERS will be bypassed as long as the RF module is connected
//                to the LINK_AT_STARTUP host for that particular module
//                Fixed up ONLY_LINK_UNLINK Logic - to ensure that if ONLY_LINK_UNLINK=Y then only
//                named / spec'd callsigns can link/unlink - all other users are denied linking / unlinking
//
// Version 3.13 - Ramesh Dhami, VA3UV - 2014.02.18
//                Added RF inactivity timer:  tracing[i].last_time
//                Added 3 new variables to the cfg file:  RF_INACTIVITY_TIMER_A / B / C
//                Create up to 3 separate files 'local_rf_use_A/B/C' so that the external persistent_link script
//                can sense when the GW is being used locally.  The timestamp on these 3 files is updated every time
//                a local RF user transmits
//
//
//
// version 3.12 - Ramesh Dhami, VA3UV - 2013.10.09
//                Added checks to make sure that users MyCALL is valid - check MyCALL against valid_users.txt


   


#include <stdio.h>
#include <fcntl.h>
#include <string.h>
#include <ctype.h>
#include <stdlib.h>
#include <stdarg.h>
#include <unistd.h>
#include <signal.h>
#include <errno.h>
#include <time.h>
#include <sys/time.h>

#include <regex.h>

#include <sys/stat.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <sys/ioctl.h>

#include <netinet/ip.h>
#include <netinet/udp.h>
#include <net/if.h>
#include <netpacket/packet.h>
#include <net/ethernet.h>

#include <netinet/in.h>
#include <arpa/inet.h>
#include <netdb.h>

#include <pthread.h>

/* Required for Binary search trees using C++ STL */
#include <string>
#include <set>
#include <map>
#include <utility>
using namespace std;

/*** version number must be x.xx ***/
#define VERSION "4.00"

#define CALL_SIZE 8
#define IP_SIZE 15
#define QUERY_SIZE 56
#define MAXHOSTNAMELEN 64
#define TIMEOUT 50
#define LINK_CODE 'O'
#define UNLINK_CODE 'T'
#define INFO_CODE 'W'

#define DONGLE_CODE 'D'
#define FILE_REFRESH_GWYS_CODE 'F'

#define RESTORE_TIMER_CODE 'R'
#define RESET_TIMER_CODE 'Z'

/* configuration data */
static char OWNER[CALL_SIZE + 1];
static char ADMIN[CALL_SIZE + 1];
static bool ONLY_ADMIN_LOGIN = false;
static char LINK_UNLINK_USER[CALL_SIZE + 1];
static bool ONLY_LINK_UNLINK = false;
static bool unlink_token = true;
static int ONLY_LINK_UNLINK_temp = 0;
static char EXTERNAL_IF[IF_NAMESIZE + 1];
static char LISTEN_IP[IP_SIZE + 1];
static int G2_EXTERNAL_PORT = 40000;
static char INTERNAL_IF[IF_NAMESIZE + 1];
static uint16_t G2_INTERNAL_PORT = htons(20000);
static uint16_t RP2C_PORT = htons(20000);
static int RMT_XRF_PORT = 30001;
static int RMT_REF_PORT = 50001;
static int RMT_DCS_PORT = 30051;
static int COMMAND_PORT = 30003;
static bool QSO_DETAILS = false;
static char GWYS[FILENAME_MAX + 1];
static char VALID_CALLSIGNS[FILENAME_MAX + 1];
static char STATUS_FILE[FILENAME_MAX + 1];
static bool ANNOUNCE = false;
static char ANNOUNCE_DIR[FILENAME_MAX + 1];
static bool RPTR_ACK = true;
static int DELAY_BETWEEN = 18;
static int DELAY_BEFORE = 3;
static char LINK_AT_STARTUP_A[CALL_SIZE + 1];
static char LINK_AT_STARTUP_A_TMP[CALL_SIZE + 1];
static char LINK_AT_STARTUP_B[CALL_SIZE + 1];
static char LINK_AT_STARTUP_B_TMP[CALL_SIZE + 1];
static char LINK_AT_STARTUP_C[CALL_SIZE + 1];
static char LINK_AT_STARTUP_C_TMP[CALL_SIZE + 1];
static unsigned int MAX_DONGLES = 5;
static unsigned int SAVED_MAX_DONGLES = 5;
//static char REPORTS[MAXHOSTNAMELEN + 1];
//static char AUTH0[MAXHOSTNAMELEN + 1];
//static char AUTH1[MAXHOSTNAMELEN + 1];
//static char AUTH2[MAXHOSTNAMELEN + 1];
// v3.18 - no longer used static char ECHOTEST_DIR[FILENAME_MAX + 1];
// v3.18 - no longer used static int ECHOTEST_REC_TIMEOUT = 1;
static long RF_INACTIVITY_TIMER[3] = { 3, 3, 3 };
static long RF_INACTIVITY_TIMER_SAVE[3] = { 3, 3, 3};

static unsigned char REF_ACK[3] = { 3, 96, 0 };
static char RF_FLAGS_DIR[FILENAME_MAX + 1];


char my_module[2];
char dest_mod[2];
char test[9];
char rf_file[40];  /* Touch a file in the /tmp folder to mark when the repeater was last used */
char uv_mod[2];    /* Preserve the module where the RF user was last heard */
char uv_rf_module; /* Module where a user was last heard */
int uv_count_a;
int uv_count_b;

char temp_buff[10];
char temp_buff_a[11];
char temp_buff_b[11];
char temp_buff_c[11];

/* 
   This is the data payload in the map: inbound_list
   This is for inbound dongles
*/
struct inbound
{
   /* the callsign of the remote */
   char call[CALL_SIZE + 1];

   /* IP and port of remote */
   struct sockaddr_in sin;

   /* if countdown expires, the connection is terminated */
   short countdown;

   /* This user talked on this module */
   char mod;  /* A B C */

   /* dvap, dvdongle, ... */
   char client;

};
/* the Key in this inbound_list map is the unique IP address of the remote */
typedef map<string, inbound *> inbound_type;
static inbound_type inbound_list;

typedef set<string> admin_type;
static admin_type admin;

typedef set<string> link_unlink_user_type;
static link_unlink_user_type link_unlink_user;

#define LH_MAX_SIZE 39
typedef map<string, string> dt_lh_type;
static dt_lh_type dt_lh_list;

/*
   to_remote_g2 contains the remote repeaters/reflectors
     that our local bands are linked with.
   The remote systems can be either:
      XRF-type or REF-type or DCS-type
 
   index 0 is from_mod=A,
   index 1 is from_mod=B,
   index 2 is from_mod=C 
*/
static struct
{
   char type; /* p or x or d */
   char link_status[CALL_SIZE + 1];
   char to_call[CALL_SIZE + 1];
   struct sockaddr_in toDst4;
   char from_mod;
   char to_mod;
   short countdown;
   bool is_connected;
   unsigned char in_streamid[2];  /* incoming from remote systems */
   unsigned char out_streamid[2]; /* outgoing to remote systems */
} to_remote_g2[3];

static struct
{
   unsigned char streamid[2];
   uint32_t adr;
} plus_crap[3] = { { {0x00, 0x00}, 0 },
                   { {0x00, 0x00}, 0 },
                   { {0x00, 0x00}, 0 } };

/* broadcast for data arriving from xrf to local rptr */
static struct
{
   unsigned char xrf_streamid[2]; /* streamid from xrf */
   unsigned char rptr_streamid[2][2];  /* generated streamid to rptr(s) */
} brd_from_xrf;
static unsigned char from_xrf_torptr_brd[56];
static short brd_from_xrf_idx = 0;

/* broadcast for data arriving from ref to local rptr */
static struct
{
   unsigned char ref_streamid[2]; /* streamid from ref */
   unsigned char rptr_streamid[2][2];  /* generated streamid to rptr(s) */
} ml_from_ref;
static unsigned char from_ref_torptr_brd[58];
static short ml_from_ref_idx = 0;

/* broadcast for data arriving from local rptr */
static struct
{
   unsigned char from_rptr_streamid[2];
   unsigned char to_rptr_streamid[2][2];
} ml_from_rptr;
static unsigned char multilink[58];
static short ml_from_rptr_idx = 0;

/* This is for echotest */

//v3.18 static struct
//{
//   time_t last_time;
//   unsigned char streamid[2];
//   int fd;
//   char file[FILENAME_MAX + 1];
//} recd[3]; /* local module 0, 1, 2 */
//static unsigned char recbuf[100]; /* 56 or 27, max is 56 */
//static short int rec_len = 56;
//static long num_recs = 0L;
//static pthread_t echo_thread;
//static pthread_attr_t echo_attr;



/* 
   index 0 is local mod=A,
   index 1 is local mod=B,
   index 2 is local mod=C
*/
static struct
{
   unsigned char streamid[2];
   time_t last_time; /* last time RF user talked */
} tracing[3] = { { {0,0}, 0 },
                 { {0,0}, 0 },
                 { {0,0}, 0 } };

/* input from remote */
static int xrf_g2_sock = -1;
static int ref_g2_sock = -1;
static int dcs_g2_sock = -1;
static unsigned char dcs_buf[1000];
static unsigned char readBuffer2[1024]; 
static struct sockaddr_in fromDst4;
/* 
   After we receive it from remote g2, 
   we must feed it to our local repeater.
*/
static struct sockaddr_in toLocalg2;

/* input from our own local repeater */
static int rptr_sock = -1;
static unsigned char readBuffer[1024]; /* 58 or 29 or 32, max is 58 */
static struct sockaddr_ll sll;
static u_char *udp_payload;
static int udp_payload_len;
static uint32_t internal_daddr = 0;

/* input from command port */
static int cmd_sock = -1;
static struct sockaddr_in fromCmd;

static fd_set fdset;
static struct timeval tv;

static bool keep_running = true;

/* auth stuff */
static sockaddr_in to_reports;
static struct start_msg_to_reports
{
   unsigned char codes[4];
   char version[10];
   char sep1;
   char gw[15];
   char sep2;
   char time[22];
   char sep3;
   char type[6];
   char sep4;
   char mod[11];
   char sep5;
   unsigned char streamid[13];
   char sep6;
   char my[15];
   char sep7;
   char sfx[13];
   char sep8;
   char yr[15];
   char sep9;
   char rpt1[13];
   char sep10;
   char rpt2[13];
   char sep11;
   char msg[20];
   char sep12;
   char id[5];
} sm_to_r;
//v3.18 static sockaddr_in to_auth0;
//static sockaddr_in to_auth1;
//static sockaddr_in to_auth2;

/* last 4 bytes is seed */
//v3.18 static unsigned char rep_from_auth0_ok[9] = {0x09, 0x00, 0x18, 0x00, 0x02, 0x00, 0x00, 0x00, 0x00};
/* last 4 bytes is seed */
//v3.18 static unsigned char rep_from_auth1_ok[9] = {0x09, 0x00, 0x18, 0x00, 0x02, 0x00, 0x00, 0x00, 0x00};  
/* the last 4 bytes are:  "22j " */
//v3.18 static unsigned char rep_to_auth_ok[9] = {0x09, 0x00, 0x18, 0x00, 0x02, 0x32, 0x32, 0x6a, 0x20};
//v3.18 static bool auth0_linking_ok = false;
//v3.18 static bool auth1_linking_ok = false;
/* static struct auth_msg_to_auth
{
   unsigned char codes[4];
   char auth_type[14];
   char sep1;
   char proto[7];
   char sep2;
   char prog[10];
   char sep3;
   char version[12];
   char sep4;
   char gw[15];
   char sep5;
   char id[4];
   char term;
} am_to_a;

*/

// v3.18 static time_t au_msg_time = 0;

/* Used to validate incoming donglers */
static regex_t preg;

const char* G2_html = "<table border=\"0\" width=\"95%\"><tr>"
                                   "<td width=\"4%\"><img border=\"0\" src=g2ircddb.jpg></td>"
                                   "<td width=\"96%\"><font size=\"2\">"
                                   "<b>REPEATER</b> G2_LINK v4.00"
                                   "</font></td>"
                                   "</tr></table>";

/* re-transmit headers to plus on SYNC */
static struct {
   unsigned char buf[58];
} regen_hdr_for_plus_refs[3];
static struct {
   unsigned char buf[58];
   unsigned streamid[2];
} regen_hdr_for_plus_dongles[3];

static unsigned short crc_tabccitt[256] =
{
   0x0000,0x1189,0x2312,0x329b,0x4624,0x57ad,0x6536,0x74bf,
   0x8c48,0x9dc1,0xaf5a,0xbed3,0xca6c,0xdbe5,0xe97e,0xf8f7,
   0x1081,0x0108,0x3393,0x221a,0x56a5,0x472c,0x75b7,0x643e,
   0x9cc9,0x8d40,0xbfdb,0xae52,0xdaed,0xcb64,0xf9ff,0xe876,
   0x2102,0x308b,0x0210,0x1399,0x6726,0x76af,0x4434,0x55bd,
   0xad4a,0xbcc3,0x8e58,0x9fd1,0xeb6e,0xfae7,0xc87c,0xd9f5,
   0x3183,0x200a,0x1291,0x0318,0x77a7,0x662e,0x54b5,0x453c,
   0xbdcb,0xac42,0x9ed9,0x8f50,0xfbef,0xea66,0xd8fd,0xc974,
   0x4204,0x538d,0x6116,0x709f,0x0420,0x15a9,0x2732,0x36bb,
   0xce4c,0xdfc5,0xed5e,0xfcd7,0x8868,0x99e1,0xab7a,0xbaf3,
   0x5285,0x430c,0x7197,0x601e,0x14a1,0x0528,0x37b3,0x263a,
   0xdecd,0xcf44,0xfddf,0xec56,0x98e9,0x8960,0xbbfb,0xaa72,
   0x6306,0x728f,0x4014,0x519d,0x2522,0x34ab,0x0630,0x17b9,
   0xef4e,0xfec7,0xcc5c,0xddd5,0xa96a,0xb8e3,0x8a78,0x9bf1,
   0x7387,0x620e,0x5095,0x411c,0x35a3,0x242a,0x16b1,0x0738,
   0xffcf,0xee46,0xdcdd,0xcd54,0xb9eb,0xa862,0x9af9,0x8b70,
   0x8408,0x9581,0xa71a,0xb693,0xc22c,0xd3a5,0xe13e,0xf0b7,
   0x0840,0x19c9,0x2b52,0x3adb,0x4e64,0x5fed,0x6d76,0x7cff,
   0x9489,0x8500,0xb79b,0xa612,0xd2ad,0xc324,0xf1bf,0xe036,
   0x18c1,0x0948,0x3bd3,0x2a5a,0x5ee5,0x4f6c,0x7df7,0x6c7e,
   0xa50a,0xb483,0x8618,0x9791,0xe32e,0xf2a7,0xc03c,0xd1b5,
   0x2942,0x38cb,0x0a50,0x1bd9,0x6f66,0x7eef,0x4c74,0x5dfd,
   0xb58b,0xa402,0x9699,0x8710,0xf3af,0xe226,0xd0bd,0xc134,
   0x39c3,0x284a,0x1ad1,0x0b58,0x7fe7,0x6e6e,0x5cf5,0x4d7c,
   0xc60c,0xd785,0xe51e,0xf497,0x8028,0x91a1,0xa33a,0xb2b3,
   0x4a44,0x5bcd,0x6956,0x78df,0x0c60,0x1de9,0x2f72,0x3efb,
   0xd68d,0xc704,0xf59f,0xe416,0x90a9,0x8120,0xb3bb,0xa232,
   0x5ac5,0x4b4c,0x79d7,0x685e,0x1ce1,0x0d68,0x3ff3,0x2e7a,
   0xe70e,0xf687,0xc41c,0xd595,0xa12a,0xb0a3,0x8238,0x93b1,
   0x6b46,0x7acf,0x4854,0x59dd,0x2d62,0x3ceb,0x0e70,0x1ff9,
   0xf78f,0xe606,0xd49d,0xc514,0xb1ab,0xa022,0x92b9,0x8330,
   0x7bc7,0x6a4e,0x58d5,0x495c,0x3de3,0x2c6a,0x1ef1,0x0f78
};

/* the map of the loaded entries in gwys.txt */
/* key is the callsign, data is the host and port */
typedef map<string, string> gwy_list_type;
static gwy_list_type gwy_list;

/* This is the map above, but the key is the ip */
typedef map<string, string> ip_list_type;
static ip_list_type ip_list;

/* the list of the loaded entries in valid_callsigns.txt */
typedef set<string> valid_callsigns_type;
static valid_callsigns_type valid_callsigns;

static unsigned char queryCommand[QUERY_SIZE];

/* dtmf stuff */
static char silence[9] = { 0x4e,0x8d,0x32,0x88,0x26,0x1a,0x3f,0x61,0xe8 };
static char DTMF_DIR[FILENAME_MAX + 1];
static char DTMF_FILE[FILENAME_MAX + 1];
static const int MAX_DTMF_BUF = 32;
static char dtmf_chars[17] = "147*2580369#ABCD";
static int dtmf_digit;
static FILE *dtmf_fp = NULL;
static char dtmf_buf[3][MAX_DTMF_BUF + 1] = { {""}, {""}, {""} };
static int dtmf_buf_count[3] = {0, 0, 0};
static unsigned int dtmf_counter[3] = {0, 0, 0};
static int dtmf_last_frame[3] = {0, 0, 0};
static char dtmf_mycall[3][CALL_SIZE + 1] = { {""}, {""}, {""} };
extern void dstar_dv_init();
extern int dstar_dv_decode(const unsigned char *d, int data[3]);

/* START:  TEXT crap */
static bool new_group[3] = { true, true, true };
static int header_type = 0;
static bool GPS_seen[3] = { false, false, false };
unsigned char tmp_txt[3];
static char *p_tmp2 = NULL;
/* END:  TEXT crap */

/* this is used for the "dashboard and QSO_DETAILS" to avoid processing multiple headers */
static struct
{
   unsigned char sid[2];
} old_sid[3] = { { {0x00, 0x00} },
                 { {0x00, 0x00} },
                 { {0x00, 0x00} } };

static bool load_gwys(char *filename);
static bool load_valid_callsigns(char *filename);
static void calcPFCS(unsigned char *packet, int len);
static void traceit(const char *fmt,...);
static bool read_config(char *);
static bool srv_open();
static void srv_close();
static void sigCatch(int signum);
static void g2link(char from_mod, char *call, char to_mod);
static void runit();
static void print_status_file();
static void print_status_screen();
static void send_heartbeat();
static void handle_cmd(char *buf);
static bool resolve_plus();
static void link_plus(short int i);
//static void *echotest(void *arg);
static bool resolve_rmt(char *name, int type, struct sockaddr_in *addr);

static void audio_notify(char *notify_msg);
static void rptr_ack(short i);

static void *audio_notify_run(void *arg);
static void *rptr_ack_run(void *arg);

static void dv_block(char mod);
static bool df_check(char mod);

// v3.18

static bool df_check(char mod)
{
   char df_s[FILENAME_MAX + 1];
   FILE *df_fp = NULL;
   char df_buf[256];
   char msg[] = {" Linked to  "};
   bool ok = true;

   msg[11] = mod;
   strcpy(df_s, "/dstar/tmp/status");
   df_fp = fopen(df_s, "r");
   if (df_fp == NULL)
      return true;

   while (fgets(df_buf, 254, df_fp) != NULL)
   {
      if (strstr(df_buf, msg) != NULL)
      {
         traceit("%s", df_buf);
         ok = false;
         break;
      }
   }
   fclose(df_fp);

   return ok;
}

static void df_block(char mod)
{
   char df_b[FILENAME_MAX + 1];
   int fd = -1;

   sprintf(df_b, "/dstar/tmp/blocklinking-%c", mod);
   fd = open(df_b, O_WRONLY | O_CREAT | O_EXCL, S_IRUSR | S_IWUSR);
   if (fd >= 0)
   {
      close(fd);
      fd = -1;
   }
   return;
}


static bool resolve_rmt(char *name, int type, struct sockaddr_in *addr)
{
   struct addrinfo hints;
   struct addrinfo *res;
   struct addrinfo *rp;
   int rc = 0;
   bool found = false;

   memset(&hints, 0x00, sizeof(struct addrinfo));
   hints.ai_family = AF_INET;
   hints.ai_socktype = type;

   rc = getaddrinfo(name, NULL, &hints, &res);
   if (rc != 0)
   {
      traceit("getaddrinfo return error code %d for [%s]\n", rc, name);
      return false;
   }

   for (rp = res; rp != NULL; rp = rp->ai_next)
   {
      if ((rp->ai_family == AF_INET) &&
          (rp->ai_socktype == type))
      {
         memcpy(addr, rp->ai_addr, sizeof(struct sockaddr_in));
         found = true;
         break;
      }
   }
   freeaddrinfo(res);
   return found;
}

/* v3.18

static void *echotest(void *arg)
{
   char *file = (char *)arg;
   struct timespec req;

   FILE *fp = NULL;
   unsigned short rlen = 0;
   size_t nread = 0;
   unsigned char dstar_buf[56];
   struct sigaction act;

   act.sa_handler = sigCatch;
   sigemptyset(&act.sa_mask);
   act.sa_flags = SA_RESTART;
   if (sigaction(SIGTERM, &act, 0) != 0)
   {
      traceit("sigaction-TERM failed, error=%d\n", errno);
      traceit("echotest thread exiting...\n");
      pthread_exit(NULL);
   }
   if (sigaction(SIGINT, &act, 0) != 0)
   {
      traceit("sigaction-INT failed, error=%d\n", errno);
      traceit("echotest thread exiting...\n");
      pthread_exit(NULL);
   }

   fp = fopen(file, "rb");
   if (!fp)
   {
      traceit("Failed to open file %s\n", file);
      pthread_exit(NULL);
   }

   nread = fread(dstar_buf, 10, 1, fp);
   if (nread != 1)
   {
      traceit("Cant read first 10 bytes in %s\n", file);
      fclose(fp);
      pthread_exit(NULL);
   }

   if (memcmp(dstar_buf, "DVTOOL", 6) != 0)
   {
      traceit("DVTOOL keyword not found in %s\n", file);
      fclose(fp);
      pthread_exit(NULL);
   }

   sleep(DELAY_BEFORE);
   traceit("File to playback:[%s]\n", file);

   while (keep_running)
   {
      nread = fread(&rlen, 2, 1, fp);
      if (nread != 1)
         break;

      if ((rlen != 56) && (rlen != 27))
      {
         traceit("Expected 56 bytes or 27 bytes, found %d\n", rlen);
         break;
      }
      nread = fread(dstar_buf, rlen, 1, fp);
      if (nread == 1)
      {
         if (memcmp(dstar_buf, "DSVT", 4) != 0)
         {
            traceit("DVST keyword not found in %s\n", file);
            break;
         }

         if (dstar_buf[8] != 0x20)
         {
            traceit("Not Voice type in %s\n", file);
            break;
         }

         if ((dstar_buf[4] != 0x10) && (dstar_buf[4] != 0x20))
         {
            traceit("Not a valid record type in %s\n",file);
            break;
         }

         sendto(ref_g2_sock, (char *)dstar_buf, rlen, 0,
                (struct sockaddr *)&toLocalg2,sizeof(toLocalg2));

         req.tv_sec = 0;
         req.tv_nsec = DELAY_BETWEEN * 1000000;
         nanosleep(&req, NULL);
      }
   }
   fclose(fp);
   unlink(file);

   traceit("Finished playing\n");
   pthread_exit(NULL);
}

*/


/* Process the shell command */
static void handle_cmd(char *buf)
{
   char reply[24];
   char *p = NULL;
   char call[CALL_SIZE + 1];
   char cmd[4];
   short i,j;
   char nak[5];
   char *ptr_cmd = NULL;
   char *ptr_call = NULL;
   char temp_repeater[CALL_SIZE + 1];
   const char *delim = " ";
   char unlink_request[19];
   char notify_msg[64];
   char *space_p = 0;
   char linked_remote_system[CALL_SIZE + 1];

//v3.18
   char df_b[FILENAME_MAX + 1];
//

   nak[0] = '\0';

   p = strchr(buf, '\r');
   if (p)
      *p = '\0';

   p = strchr(buf, '\n');
   if (p)
      *p = '\0';

   traceit("Received command [%s] from [%s]\n", buf, inet_ntoa(fromCmd.sin_addr));

   if (strlen(buf) < 2)
   {
      traceit("Invalid command length\n");
      strcpy(nak, "NAK\n");
   }
   else
   {
      if (strcmp(buf, "sh") == 0)  /* shut it down */
         keep_running = false;
      else
      if (strcmp(buf, "qsoy") == 0)  /* QSO_DETAILS yes */
         QSO_DETAILS = true;
      else
      if (strcmp(buf, "qson") == 0) /* QSO_DETAILS no */
         QSO_DETAILS = false;
      else
      if (strcmp(buf, "pv") == 0)   /* print version */
      {
         snprintf(reply, 23, "%s\n", VERSION);
         sendto(cmd_sock, reply, strlen(reply),
                0, (struct sockaddr *)&fromCmd,
                sizeof(struct sockaddr_in));
      }
      else
      if (strcmp(buf, "ps") == 0)   /* print status */
         print_status_screen();
      else
      if (strcmp(buf, "rfr") == 0) 
      {
         load_gwys(GWYS);
         load_valid_callsigns(VALID_CALLSIGNS);
      }
      else
      {
         ptr_cmd = strtok(buf, delim);
         if (ptr_cmd)
            ptr_call = strtok(NULL, delim);

         if (!ptr_cmd || !ptr_call)
         {
            traceit("Invalid command\n");
            strcpy(nak, "NAK\n");
         }
         else
         if ((strlen(ptr_cmd) > 2) || (strlen(ptr_call) > CALL_SIZE))
         {
            traceit("Invalid command length\n");
            strcpy(nak, "NAK\n");
         }
         else
         {
            strcpy(cmd, ptr_cmd);
            strcpy(call, ptr_call);

            traceit("cmd=[%s], parameter=[%s]\n", cmd, call);

            /*
               Link command: the second parameter must be 8 characters: localMod Repeater remoteMod
               Example: lm CXRF003A
               Example: lm CK1XC__B    (you must use _ if the callsign is less than 6)
            */
            if (strcmp(cmd, "lm") == 0)
            {
               if (strlen(call) != CALL_SIZE)
               {
                  traceit("Invalid parameter length\n");
                  strcpy(nak, "NAK\n");
               }
               else
               {
                  /* replace _ with SPACE */
                  for (i = 0; i < CALL_SIZE; i++)
                  {
                     if (call[i] == '_')
                        call[i] = ' ';
                  }
                  memset(temp_repeater, ' ', CALL_SIZE);
                  memcpy(temp_repeater, call + 1, 6);
                  temp_repeater[8] = '\0';

                  if ((call[0] != 'A') && (call[0] != 'B') && (call[0] != 'C'))
                  {
                     traceit("Invalid local module\n");
                     strcpy(nak, "NAK\n");
                  }
                  else
                  {
                     i = -1;
                     if (call[0] == 'A')
                        i = 0;
                     else
                     if (call[0] == 'B')
                        i = 1;
                     else
                     if (call[0] == 'C')
                        i = 2;

// 3.18
                     if (strncmp(temp_repeater, "REF", 2) == 0)
                     {
                       traceit("Trying to link to an REF - that is no longer supported\n");
                       i = -1;
                       strcpy(nak, "NAK\n");
                     }

                     if (i >= 0)
                     {
                        if ((to_remote_g2[i].to_call[0] == '\0') ||   /* not linked */
                            ((to_remote_g2[i].to_call[0] != '\0') &&  /* waiting for a link reply that may never arrive */
                            !to_remote_g2[i].is_connected))
                           g2link(call[0], temp_repeater, call[7]);
                        else
                        {
                           traceit("Module is active, unlink before you link\n");
                           strcpy(nak, "NAK\n");
                        }
                     }
                  }
               }
            }
            else
            if (strcmp(cmd, "in") == 0)   // Info on link status
            {
               if (strlen(call) != 1)
               {
                  traceit("Invalid parameter length\n");
                  strcpy(nak, "NAK\n");
               }
               else
               if ((call[0] != 'A') && (call[0] != 'B') && (call[0] != 'C'))
               {
                  traceit("Invalid local module\n");
                  strcpy(nak, "NAK\n");
               }
               else
               {
                  i = -1;
                  if (call[0] == 'A')
                     i = 0;
                  else
                  if (call[0] == 'B')
                     i = 1;
                  else
                  if (call[0] == 'C')
                     i = 2;

                  if (i >= 0)
                  {
                     if (to_remote_g2[i].is_connected)
                     {
                        tracing[i].last_time = time(NULL);  //VA3UV
                        strcpy(linked_remote_system, to_remote_g2[i].to_call);
                        space_p = strchr(linked_remote_system, ' ');
                        if (space_p)
                           *space_p = '\0';
                        sprintf(notify_msg, "%c_linked.dat_LINKED_%s_%c",
                                to_remote_g2[i].from_mod,
                                linked_remote_system,
                                to_remote_g2[i].to_mod);
                     }
                     else
                        sprintf(notify_msg, "%c_unlinked.dat_UNLINKED", call[0]);
                     audio_notify(notify_msg);
                  }
               }
            }
            else
            if (strcmp(cmd, "um") == 0)
            {
               if (strlen(call) != 1)
               {
                  traceit("Invalid parameter length\n");
                  strcpy(nak, "NAK\n");
               }
               else
               if ((call[0] != 'A') && (call[0] != 'B') && (call[0] != 'C'))
               {
                  traceit("Invalid local module\n");
                  strcpy(nak, "NAK\n");
               }
               else
               {
                  i = -1;
                  if (call[0] == 'A')
                     i = 0;
                  else
                  if (call[0] == 'B')
                     i = 1;
                  else
                  if (call[0] == 'C')
                     i = 2;

                  if (i >= 0)
                  {
                     if (to_remote_g2[i].to_call[0] != '\0')
                     {
                        traceit("Unlinking from [%s] mod %c\n",
                                to_remote_g2[i].to_call, to_remote_g2[i].to_mod);

                        sprintf(notify_msg, "%c_unlinked.dat_UNLINKED", to_remote_g2[i].from_mod);

                        // v3.18

                        sprintf(df_b, "/dstar/tmp/blocklinking-%c", tolower(to_remote_g2[i].from_mod));
                        unlink(df_b);

                        if (to_remote_g2[i].type == 'p')
                        {
                           queryCommand[0] = 0x05;
                           queryCommand[1] = 0x00;
                           queryCommand[2] = 0x18;
                           queryCommand[3] = ((to_remote_g2[i].from_mod - 'A') << 4) | (to_remote_g2[i].to_mod - 'A');
                           queryCommand[4] = 0x00;
                           for (j = 0; j < 3; j++)
                              sendto(ref_g2_sock,(char *)queryCommand,5,0,
                                     (struct sockaddr *)&(to_remote_g2[i].toDst4),
                                     sizeof(to_remote_g2[i].toDst4));
                        }
                        else
                        if (to_remote_g2[i].type == 'x')
                        {
                           strcpy(unlink_request, OWNER);
                           unlink_request[8] = to_remote_g2[i].from_mod;
                           unlink_request[9] = ' ';
                           unlink_request[10] = '\0';

                           for (j = 0; j < 5; j++)
                              sendto(xrf_g2_sock,unlink_request, CALL_SIZE + 3,0,
                                     (struct sockaddr *)&(to_remote_g2[i].toDst4),
                                     sizeof(to_remote_g2[i].toDst4));
                        }
                        else
                        if (to_remote_g2[i].type == 'd')
                        {
                           strcpy(unlink_request, OWNER);
                           unlink_request[8] = to_remote_g2[i].from_mod;
                           unlink_request[9] = ' ';
                           unlink_request[10] = '\0';
                           memcpy(unlink_request + 11, to_remote_g2[i].to_call, 8);

                           for (j = 0; j < 5; j++)
                              sendto(dcs_g2_sock,unlink_request, 19,0,
                                     (struct sockaddr *)&(to_remote_g2[i].toDst4),
                                     sizeof(to_remote_g2[i].toDst4));
                        }

                        /* now zero out this entry */
                        to_remote_g2[i].type = ' ';
                        to_remote_g2[i].to_call[0] = '\0';
                        memset(&(to_remote_g2[i].toDst4),0,sizeof(struct sockaddr_in));
                        to_remote_g2[i].from_mod = ' ';
                        to_remote_g2[i].to_mod = ' ';
                        to_remote_g2[i].countdown = 0;
                        to_remote_g2[i].is_connected = false;
                        to_remote_g2[i].in_streamid[0] = 0x00;
                        to_remote_g2[i].in_streamid[1] = 0x00;

                        print_status_file();
                        audio_notify(notify_msg);
                     }
                  }
               }
            }
            else
            {
               traceit("Invalid command\n");
               strcpy(nak, "NAK\n");
            }
         }
      }
   }

   if (nak[0] == '\0')
      strcpy(nak, "OK\n");

   sendto(cmd_sock,nak,4,
          0, (struct sockaddr *)&fromCmd,
          sizeof(struct sockaddr_in));
   return;

}

/* send keepalive to donglers */
static void send_heartbeat()
{
   inbound_type::iterator pos;
   inbound *inbound_ptr;
   bool removed = false;
   
   for (pos = inbound_list.begin(); pos != inbound_list.end(); pos++)
   {
      inbound_ptr = (inbound *)pos->second;
      sendto(ref_g2_sock,(char *)REF_ACK,3,0,
             (struct sockaddr *)&(inbound_ptr->sin),
             sizeof(struct sockaddr_in));

      if (inbound_ptr->countdown >= 0)
         inbound_ptr->countdown --;

      if (inbound_ptr->countdown < 0)
      {
         removed = true;
         traceit("call=%s timeout, removing %s, users=%d\n",
                 inbound_ptr->call, 
                 pos->first.c_str(),
                 inbound_list.size() - 1);

         free(pos->second);
         pos->second = NULL;
         inbound_list.erase(pos);
      }
   }
   if (removed)
      print_status_file();
}

static void rptr_ack(short i)
{
   pthread_t rptr_ack_thread;
   pthread_attr_t attr;
   int rc = 0;
   static char mod_and_RADIO_ID[3][22];

   memset(mod_and_RADIO_ID[i], ' ', 21);
   mod_and_RADIO_ID[i][21] = '\0';
   

   if (i == 0)
      mod_and_RADIO_ID[i][0] = 'A';
   else
   if (i == 1)
      mod_and_RADIO_ID[i][0] = 'B';
   else
   if (i == 2)
      mod_and_RADIO_ID[i][0] = 'C';

   if (to_remote_g2[i].is_connected)
   {
      memcpy(mod_and_RADIO_ID[i] + 1, "LINKED TO ", 10);
      memcpy(mod_and_RADIO_ID[i] + 11, to_remote_g2[i].to_call, CALL_SIZE);
      mod_and_RADIO_ID[i][11 + CALL_SIZE] = to_remote_g2[i].to_mod;
   }
   else
   if (to_remote_g2[i].to_call[0] != '\0')
   {
      memcpy(mod_and_RADIO_ID[i] + 1, "TRYING    ", 10);
      memcpy(mod_and_RADIO_ID[i] + 11, to_remote_g2[i].to_call, CALL_SIZE);
      mod_and_RADIO_ID[i][11 + CALL_SIZE] = to_remote_g2[i].to_mod;
   }
   else

      memcpy(mod_and_RADIO_ID[i] + 1, "NOT LINKED", 10);

   pthread_attr_init(&attr);
   pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED);
   rc = pthread_create(&rptr_ack_thread, &attr, rptr_ack_run, (void *)(mod_and_RADIO_ID[i]));
   if (rc != 0)
      traceit("failed to start rptr_ack thread for mod %c\n", mod_and_RADIO_ID[i][0]);
   pthread_attr_destroy(&attr);
   return;
}

static void *rptr_ack_run(void *arg)
{
   char from_mod = *((char *)arg);
   char RADIO_ID[21];
   memcpy(RADIO_ID, (char *)arg + 1, 21);
   unsigned char rptr_ack[56];
   struct timespec nanos;
   unsigned int aseed;
   time_t tnow = 0;
   char silence[12] =
   {
      0x4e,0x8d,0x32,0x88,0x26,0x1a,0x3f,0x61,0xe8,
      0x70,0x4f,0x93
   };
   struct sigaction act;

   act.sa_handler = sigCatch;
   sigemptyset(&act.sa_mask);
   act.sa_flags = SA_RESTART;
   if (sigaction(SIGTERM, &act, 0) != 0)
   {
      traceit("sigaction-TERM failed, error=%d\n", errno);
      traceit("rptr_ack thread exiting...\n");
      pthread_exit(NULL);
   }
   if (sigaction(SIGINT, &act, 0) != 0)
   {
      traceit("sigaction-INT failed, error=%d\n", errno);
      traceit("rptr_ack thread exiting...\n");
      pthread_exit(NULL);
   }
   
   time(&tnow);
   aseed = tnow + pthread_self();
   
   u_int16_t streamid_raw = (::rand_r(&aseed) % 65535U) + 1U;

   sleep(DELAY_BEFORE);

   traceit("sending ACK+text, mod:[%c], RADIO_ID=[%s]\n", from_mod, RADIO_ID);

   memcpy(rptr_ack,"DSVT", 4);
   rptr_ack[4] = 0x10;
   rptr_ack[5] = 0x00;
   rptr_ack[6] = 0x00;
   rptr_ack[7] = 0x00;

   rptr_ack[8] = 0x20;
   rptr_ack[9]  = 0x00;
   rptr_ack[10] = 0x01;
   rptr_ack[11] = 0x00;

   rptr_ack[12] = streamid_raw / 256U;
   rptr_ack[13] = streamid_raw % 256U;
   rptr_ack[14] = 0x80;
   rptr_ack[15] = 0x00; /* we do not want to set this to 0x01 */
   rptr_ack[16] = 0x00;
   rptr_ack[17] = 0x00;

   memcpy(rptr_ack + 18, OWNER, 8);
   rptr_ack[25] = from_mod;

   memcpy(rptr_ack + 26,  OWNER, 8);
   rptr_ack[33] = 'G';

   memcpy(rptr_ack + 34, "CQCQCQ  ", 8);

   memcpy(rptr_ack + 42, OWNER, 8);
   rptr_ack[49] = from_mod;

   memcpy(rptr_ack + 50, "RPTR", 4);
   calcPFCS(rptr_ack,56);
   (void)sendto(ref_g2_sock,(char *)rptr_ack,56,0,(struct sockaddr *)&toLocalg2,sizeof(toLocalg2));
   nanos.tv_sec = 0;
   nanos.tv_nsec = DELAY_BETWEEN * 1000000;
   nanosleep(&nanos,0);

   rptr_ack[4] = 0x20;
   memcpy((char *)rptr_ack + 15, silence, 9);

   /* start sending silence + announcement text */

   rptr_ack[14] = 0x00;
   rptr_ack[24] = 0x55;
   rptr_ack[25] = 0x2d;
   rptr_ack[26] = 0x16;
   (void)sendto(ref_g2_sock,(char *)rptr_ack,27,0,(struct sockaddr *)&toLocalg2,sizeof(toLocalg2));
   nanos.tv_sec = 0;
   nanos.tv_nsec = DELAY_BETWEEN * 1000000;
   nanosleep(&nanos,0);

   rptr_ack[14] = 0x01;
   rptr_ack[24] = '@' ^ 0x70;
   rptr_ack[25] = RADIO_ID[0] ^ 0x4f;
   rptr_ack[26] = RADIO_ID[1] ^ 0x93;
   (void)sendto(ref_g2_sock,(char *)rptr_ack,27,0,(struct sockaddr *)&toLocalg2,sizeof(toLocalg2));
   nanos.tv_sec = 0;
   nanos.tv_nsec = DELAY_BETWEEN * 1000000;
   nanosleep(&nanos,0);

   rptr_ack[14] = 0x02;
   rptr_ack[24] = RADIO_ID[2] ^ 0x70;
   rptr_ack[25] = RADIO_ID[3] ^ 0x4f;
   rptr_ack[26] = RADIO_ID[4] ^ 0x93;
   (void)sendto(ref_g2_sock,(char *)rptr_ack,27,0,(struct sockaddr *)&toLocalg2,sizeof(toLocalg2));
   nanos.tv_sec = 0;
   nanos.tv_nsec = DELAY_BETWEEN * 1000000;
   nanosleep(&nanos,0);

   rptr_ack[14] = 0x03;
   rptr_ack[24] = 'A' ^ 0x70;
   rptr_ack[25] = RADIO_ID[5] ^ 0x4f;
   rptr_ack[26] = RADIO_ID[6] ^ 0x93;
   (void)sendto(ref_g2_sock,(char *)rptr_ack,27,0,(struct sockaddr *)&toLocalg2,sizeof(toLocalg2));
   nanos.tv_sec = 0;
   nanos.tv_nsec = DELAY_BETWEEN * 1000000;
   nanosleep(&nanos,0);

   rptr_ack[14] = 0x04;
   rptr_ack[24] = RADIO_ID[7] ^ 0x70;
   rptr_ack[25] = RADIO_ID[8] ^ 0x4f;
   rptr_ack[26] = RADIO_ID[9] ^ 0x93;
   (void)sendto(ref_g2_sock,(char *)rptr_ack,27,0,(struct sockaddr *)&toLocalg2,sizeof(toLocalg2));
   nanos.tv_sec = 0;
   nanos.tv_nsec = DELAY_BETWEEN * 1000000;
   nanosleep(&nanos,0);

   rptr_ack[14] = 0x05;
   rptr_ack[24] = 'B' ^ 0x70;
   rptr_ack[25] = RADIO_ID[10] ^ 0x4f;
   rptr_ack[26] = RADIO_ID[11] ^ 0x93;
   (void)sendto(ref_g2_sock,(char *)rptr_ack,27,0,(struct sockaddr *)&toLocalg2,sizeof(toLocalg2));
   nanos.tv_sec = 0;
   nanos.tv_nsec = DELAY_BETWEEN * 1000000;
   nanosleep(&nanos,0);

   rptr_ack[14] = 0x06;
   rptr_ack[24] = RADIO_ID[12] ^ 0x70;
   rptr_ack[25] = RADIO_ID[13] ^ 0x4f;
   rptr_ack[26] = RADIO_ID[14] ^ 0x93;
   (void)sendto(ref_g2_sock,(char *)rptr_ack,27,0,(struct sockaddr *)&toLocalg2,sizeof(toLocalg2));
   nanos.tv_sec = 0;
   nanos.tv_nsec = DELAY_BETWEEN * 1000000;
   nanosleep(&nanos,0);

   rptr_ack[14] = 0x07;
   rptr_ack[24] = 'C' ^ 0x70;
   rptr_ack[25] = RADIO_ID[15] ^ 0x4f;
   rptr_ack[26] = RADIO_ID[16] ^ 0x93;
   (void)sendto(ref_g2_sock,(char *)rptr_ack,27,0,(struct sockaddr *)&toLocalg2,sizeof(toLocalg2));
   nanos.tv_sec = 0;
   nanos.tv_nsec = DELAY_BETWEEN * 1000000;
   nanosleep(&nanos,0);

   rptr_ack[14] = 0x08;
   rptr_ack[24] = RADIO_ID[17] ^ 0x70;
   rptr_ack[25] = RADIO_ID[18] ^ 0x4f;
   rptr_ack[26] = RADIO_ID[19] ^ 0x93;
   (void)sendto(ref_g2_sock,(char *)rptr_ack,27,0,(struct sockaddr *)&toLocalg2,sizeof(toLocalg2));
   nanos.tv_sec = 0;
   nanos.tv_nsec = DELAY_BETWEEN * 1000000;
   nanosleep(&nanos,0);

   rptr_ack[14] = 0x09 | 0x40;
   memset((char *)rptr_ack + 15, 0, 9);
   rptr_ack[24] = 0x70;
   rptr_ack[25] = 0x4f;
   rptr_ack[26] = 0x93;
   (void)sendto(ref_g2_sock,(char *)rptr_ack,27,0,(struct sockaddr *)&toLocalg2,sizeof(toLocalg2));
   traceit("finished sending ACK+text to mod:[%c]\n", from_mod);
   pthread_exit(NULL);
}


static void print_status_screen()
{
   struct tm tm1;
   char buf[128];
   time_t tnow;
   short i;
   inbound *inbound_ptr;
   inbound_type::iterator pos;
 
   time(&tnow);
   localtime_r(&tnow, &tm1);

   /* print connected donglers */
   for (pos = inbound_list.begin(); pos != inbound_list.end(); pos++)
   {
      inbound_ptr = (inbound *)pos->second;
      snprintf(buf, 127,
              "%c,%s,%c,%s,%02d%02d%02d,%02d:%02d:%02d\n",
              'p',
              inbound_ptr->call,
              'p',
              pos->first.c_str(),
              tm1.tm_mon+1,tm1.tm_mday,tm1.tm_year % 100,
              tm1.tm_hour,tm1.tm_min,tm1.tm_sec);

      sendto(cmd_sock, buf, strlen(buf),
             0, (struct sockaddr *)&fromCmd,
             sizeof(struct sockaddr_in));
   }
   /* print linked repeaters-reflectors */
   for (i = 0; i < 3; i++)
   {
      if (to_remote_g2[i].is_connected)
      {
         snprintf(buf, 127,
           "%c,%s,%c,%s,%02d%02d%02d,%02d:%02d:%02d\n",
            to_remote_g2[i].from_mod,
            to_remote_g2[i].to_call,
            to_remote_g2[i].to_mod,
            inet_ntoa(to_remote_g2[i].toDst4.sin_addr),
            tm1.tm_mon+1,tm1.tm_mday,tm1.tm_year % 100,
            tm1.tm_hour,tm1.tm_min,tm1.tm_sec);

         sendto(cmd_sock, buf, strlen(buf),
             0, (struct sockaddr *)&fromCmd,
             sizeof(struct sockaddr_in));
      }
   }
}

static void print_status_file()
{
   struct tm tm1;
   time_t tnow;
   FILE *statusfp = NULL;
   short i;
   inbound *inbound_ptr;
   inbound_type::iterator pos;
   
   statusfp = fopen(STATUS_FILE, "w");
   if (!statusfp)
      traceit("Failed to create status file %s\n", STATUS_FILE);
   else
   {
      setvbuf(statusfp, (char *)NULL, _IOLBF, 0);

      time(&tnow);
      localtime_r(&tnow, &tm1);

      /* print connected donglers */
      for (pos = inbound_list.begin(); pos != inbound_list.end(); pos++)
      { 
         inbound_ptr = (inbound *)pos->second;
         fprintf(statusfp,
                 "%c,%s,%c,%s,%02d%02d%02d,%02d:%02d:%02d\n",
                 'p',
                 inbound_ptr->call,
                 'p',
                 pos->first.c_str(),
                 tm1.tm_mon+1,tm1.tm_mday,tm1.tm_year % 100,
                 tm1.tm_hour,tm1.tm_min,tm1.tm_sec);
      }

      /* print linked repeaters-reflectors */ 
      for (i = 0; i < 3; i++)
      {
         if (to_remote_g2[i].is_connected)
         {
            fprintf(statusfp,
              "%c,%s,%c,%s,%02d%02d%02d,%02d:%02d:%02d\n",
               to_remote_g2[i].from_mod,
               to_remote_g2[i].to_call,
               to_remote_g2[i].to_mod,
               inet_ntoa(to_remote_g2[i].toDst4.sin_addr),
               tm1.tm_mon+1,tm1.tm_mday,tm1.tm_year % 100,
               tm1.tm_hour,tm1.tm_min,tm1.tm_sec);
         }
      }
      fclose(statusfp);
   }
}

static bool load_valid_callsigns(char *filename)
{
   FILE *fp = NULL;
   char inbuf[1024];
   char *p = NULL;
   char call[CALL_SIZE + 1];
   unsigned short i;

   valid_callsigns_type::iterator pos;

   traceit("Trying to open file %s\n", filename);
   fp = fopen(filename, "r");
   if (fp == NULL)
   {
      traceit("Failed to open file %s\n", filename);
      return false;
   }
   traceit("Opened file %s OK\n", filename);

   valid_callsigns.clear();

   while (fgets(inbuf, 1020, fp) != NULL)
   {
      p = strchr(inbuf, '\r');
      if (p)
         *p = '\0';

      p = strchr(inbuf, '\n');
      if (p)
         *p = '\0';

      p = strchr(inbuf, '#');
      if (p)
      {
         traceit("Comment line:[%s]\n", inbuf);
         continue;
      }

      memset(call, ' ', CALL_SIZE);
      call[CALL_SIZE] = '\0';

      if ((strlen(inbuf) < 3) || (strlen(inbuf) > CALL_SIZE))
         ; // traceit("user value [%s] invalid\n", inbuf);
      else
      {
         memcpy(call, inbuf, strlen(inbuf));

         for (i = 0; i < strlen(call); i++)
            call[i] = toupper(call[i]);

         /* check for duplicates */
         pos = valid_callsigns.find(call);
         if (pos == valid_callsigns.end())
         {
            if (valid_callsigns.insert(call).second)
            {
               ; // traceit("Added valid callsign [%s]\n", call);
            }
         }
      }
   }
   fclose(fp);

   traceit("Added %ld users\n", valid_callsigns.size());
   return true;
}

/* Open text file of repeaters, reflectors */
static bool load_gwys(char *filename)
{
   FILE *fp = NULL;
   char inbuf[1024];
   char *p = NULL;
   const char *delim = " ";

   char *tok;
   char call[CALL_SIZE + 1];
   char host[MAXHOSTNAMELEN + 1];
   char port[5 + 1]; 

   /* host + space + port + NULL */
   char payload[MAXHOSTNAMELEN + 1 + 5 + 1];
   unsigned short j;

   gwy_list_type::iterator gwy_pos;
   pair<gwy_list_type::iterator,bool> gwy_insert_pair;

   bool ok = false;
   struct sockaddr_in temp_addr;

   traceit("Trying to open file %s\n", filename);
   fp = fopen(filename, "r");
   if (fp == NULL)
   {
      traceit("Failed to open file %s\n", filename);
      return false;
   }
   traceit("Opened file %s OK\n", filename);

   gwy_list.clear();
   ip_list.clear();

   while (fgets(inbuf, 1020, fp) != NULL)
   {
      p = strchr(inbuf, '\r');
      if (p)
         *p = '\0';

      p = strchr(inbuf, '\n');
      if (p)
         *p = '\0';

      p = strchr(inbuf, '#');
      if (p)
      {
         traceit("Comment line:[%s]\n", inbuf);
         continue;
      }

      /* get the call */
      tok = strtok(inbuf, delim);
      if (!tok)
         continue;
      if ((strlen(tok) > CALL_SIZE) || (strlen(tok) < 3))
      {
         traceit("Invalid call [%s]\n", tok);
         continue;
      }
      memset(call, ' ', CALL_SIZE);
      call[CALL_SIZE] = '\0';
      memcpy(call, tok, strlen(tok));
      for (j = 0; j < strlen(call); j++)
         call[j] = toupper(call[j]);
      if (strcmp(call, OWNER) == 0)
      {
         traceit("Call [%s] will not be loaded\n", call); 
         continue;
      }

      /* get the host */
      tok = strtok(NULL, delim);
      if (!tok)
      {
         traceit("Call [%s] has no host\n", call); 
         continue;
      }
      strncpy(host,tok,MAXHOSTNAMELEN);
      host[MAXHOSTNAMELEN] = '\0';
      if (strcmp(host, "0.0.0.0") == 0)
      {
         traceit("call %s has invalid host %s\n", call, host);
         continue;
      }

      /* get the port */
      tok = strtok(NULL, delim);
      if (!tok)
      {
         traceit("Call [%s] has no port\n", call);
         continue;
      }
      if (strlen(tok) > 5)
      {
         traceit("call %s has invalid port [%s]\n", call, tok);
         continue;
      }
      strcpy(port, tok);
     
      /* at this point, we have: call host port */
      /* copy the payload(host port) */
      sprintf(payload, "%s %s", host, port);
     
      gwy_pos = gwy_list.find(call);
      if (gwy_pos == gwy_list.end())
      {
         gwy_insert_pair = gwy_list.insert(pair<string,string>(call,payload));
         if (gwy_insert_pair.second)
         {
            traceit("Added to host_list:  Call=[%s], payload=[%s]\n", call, payload);

            /* We will add to the ip_list ONLY gateways that are on RMT_REF_PORT */
            if ((atoi(port) == RMT_REF_PORT) && (memcmp(call, "REF", 3) != 0))
            {
               ok = resolve_rmt(host, SOCK_DGRAM, &temp_addr);
               if (!ok)
                  traceit("Could not resolve host [%s] to IP, will NOT add to ip_list\n", host);
               else
               {
                  ip_list[inet_ntoa(temp_addr.sin_addr)] = call;
                  traceit("Added to ip_list: Call=[%s], with IP=[%s]\n",call, inet_ntoa(temp_addr.sin_addr));
               }
            }
         }
         else
            traceit("Failed to add to host_list: Call=[%s], payload=[%s]\n",call, payload);
      }
      else
         traceit("Call [%s] is duplicate\n", call); 
   }
   fclose(fp);

   traceit("Added %d gateways\n", gwy_list.size());
   return true;
}

/* compute checksum */
static void calcPFCS(unsigned char *packet, int len)
{
   unsigned short crc_dstar_ffff = 0xffff;
   unsigned short tmp, short_c;
   short int i;
   short int low;
   short int high;

   if (len == 56)
   {
      low = 15;
      high = 54;
   }
   else
   if (len == 58)
   {
      low = 17;
      high = 56;
   }
   else
      return;

   for (i = low; i < high ; i++)
   {
      short_c = 0x00ff & (unsigned short)packet[i];
      tmp = (crc_dstar_ffff & 0x00ff) ^ short_c;
      crc_dstar_ffff = (crc_dstar_ffff >> 8) ^ crc_tabccitt[tmp];
   }
   crc_dstar_ffff =  ~crc_dstar_ffff;
   tmp = crc_dstar_ffff;
   // crc_dstar_ffff = (crc_dstar_ffff << 8) | (tmp >> 8 & 0xff);

   if (len == 56)
   {
      packet[54] = (unsigned char)(crc_dstar_ffff & 0xff);
      packet[55] = (unsigned char)((tmp >> 8) & 0xff);
   }
   else
   {
      packet[56] = (unsigned char)(crc_dstar_ffff & 0xff);
      packet[57] = (unsigned char)((tmp >> 8) & 0xff);
   }
   return;   
}

/* log the event */
static void traceit(const char *fmt,...)
{
   time_t ltime;
   struct tm mytm;
   const short BFSZ = 1094;
   char buf[BFSZ];

   time(&ltime);
   localtime_r(&ltime,&mytm);

   snprintf(buf,BFSZ - 1,"%02d%02d%02d at %02d:%02d:%02d:",
            mytm.tm_mon+1,mytm.tm_mday,mytm.tm_year % 100,
            mytm.tm_hour,mytm.tm_min,mytm.tm_sec);

   va_list args;
   va_start(args,fmt);
   vsnprintf(buf + strlen(buf), BFSZ - strlen(buf) - 1, fmt, args);
   va_end(args);

   fprintf(stdout, "%s", buf);

   return;
}

/* process configuration file */
static bool read_config(char *cfgFile)
{
   bool admin_found = false;
   bool link_unlink_user_found = false;
   unsigned short i = 0;
   short int valid_params = 32;
   short int params = 0;

   admin_type::iterator pos;
   link_unlink_user_type::iterator link_unlink_user_pos;

   FILE *cnf = NULL;
   char inbuf[1024];
   char *p = NULL;
   char *ptr;
   short int j;

   cnf = fopen(cfgFile, "r");
   if (!cnf)
   {
      traceit("Failed to open file %s\n", cfgFile);
      return false;
   }

   traceit("Reading file %s\n", cfgFile);
   while (fgets(inbuf, 1020, cnf) != NULL)
   {
      if (strchr(inbuf, '#'))
         continue;

      p = strchr(inbuf, '\r');
      if (p)
         *p = '\0';
      p = strchr(inbuf, '\n');
      if (p)
         *p = '\0';

      p = strchr(inbuf, '=');
      if (!p)
         continue;
      *p = '\0';

      if (strcmp(inbuf,"OWNER") == 0)
      {
          memset(OWNER,' ', sizeof(OWNER));
          OWNER[CALL_SIZE] = '\0';

          ptr = strchr(p + 1, ' ');
          if (ptr)
             *ptr = '\0';

          if ((strlen(p + 1) < 3) || (strlen(p + 1) > (CALL_SIZE - 2)))
             traceit("OWNER value [%s] invalid\n", p + 1);
          else
          {
             memcpy(OWNER, p + 1, strlen(p + 1));

             /* uppercase it */
             for (j = 0; j < CALL_SIZE; j++)
                OWNER[j] = toupper(OWNER[j]);

             traceit("OWNER=[%s]\n",OWNER);
             params ++;
          }
      }
      else
      if (strcmp(inbuf,"ADMIN") == 0)
      {
         if (!admin_found)
         {
            admin_found = true;
            params ++;
         }

         memset(ADMIN,' ', CALL_SIZE);
         ADMIN[CALL_SIZE] = '\0';

         if ( (strlen(p + 1) < 1) || (strlen(p + 1) > CALL_SIZE) )
            traceit("ADMIN value [%s] invalid\n", p + 1);
         else
         {
            memcpy(ADMIN, p + 1, strlen(p + 1));

            for (i = 0; i < strlen(ADMIN); i++)
               ADMIN[i] = toupper(ADMIN[i]);

            traceit("ADMIN=[%s]\n",ADMIN);

            /* check for duplicates */
            pos = admin.find(ADMIN);
            if (pos != admin.end())
               traceit("[%s] already an administrator\n", ADMIN);
            else
            {
               if (admin.insert(ADMIN).second)
                  traceit("[%s] is now an administrator\n", ADMIN);
               else
                  traceit("failed to add [%s] as an administrator\n", ADMIN);
            }
         }
      }
      else
      if (strcmp(inbuf,"ONLY_ADMIN_LOGIN") == 0)
      {
         if (*(p + 1) == 'Y')
            ONLY_ADMIN_LOGIN = true;
         else
            ONLY_ADMIN_LOGIN = false;
         traceit("ONLY_ADMIN_LOGIN=[%c]\n", *(p + 1));
         params ++;
      }
      else
      if (strcmp(inbuf,"LINK_UNLINK_USER") == 0)
      {
         if (!link_unlink_user_found)
         {
            link_unlink_user_found = true;
            params ++;
         }
   
         memset(LINK_UNLINK_USER,' ', CALL_SIZE);
         LINK_UNLINK_USER[CALL_SIZE] = '\0';

         if ( (strlen(p + 1) < 1) || (strlen(p + 1) > CALL_SIZE) )
            traceit("LINK_UNLINK_USER value [%s] invalid\n", p + 1);
         else
         {
            memcpy(LINK_UNLINK_USER, p + 1, strlen(p + 1));

            for (i = 0; i < strlen(LINK_UNLINK_USER); i++)
               LINK_UNLINK_USER[i] = toupper(LINK_UNLINK_USER[i]);

            traceit("LINK_UNLINK_USER=[%s]\n",LINK_UNLINK_USER);

            /* check for duplicates */
            link_unlink_user_pos = link_unlink_user.find(LINK_UNLINK_USER);
            if (link_unlink_user_pos != link_unlink_user.end())
               traceit("[%s] already in link_unlink_user list\n", LINK_UNLINK_USER);
            else
            {
               if (link_unlink_user.insert(LINK_UNLINK_USER).second)
                  traceit("[%s] added to link_unlink_user list\n", LINK_UNLINK_USER);
               else
                  traceit("failed to add [%s] to link_unlink_user list\n", LINK_UNLINK_USER);
            }
         }
      }
      else
      if (strcmp(inbuf,"ONLY_LINK_UNLINK") == 0)
      {
         if (*(p + 1) == 'Y')
            { 
              ONLY_LINK_UNLINK = true;
              ONLY_LINK_UNLINK_temp = 0;
            }   
         else
            {
            ONLY_LINK_UNLINK = false;
            ONLY_LINK_UNLINK_temp = 1;
            }
         traceit("ONLY_LINK_UNLINK=[%c]\n", *(p + 1));
         params ++;
      }
      else
      if (strcmp(inbuf,"EXTERNAL_IF") == 0)
      {
         ptr = strchr(p + 1, ' ');
         if (ptr)
            *ptr = '\0';

         if (strlen(p + 1) < 1)
            traceit("EXTERNAL_IF value [%s] invalid\n", p + 1);
         else
         {
            memset(EXTERNAL_IF, '\0', sizeof(EXTERNAL_IF));
            strncpy(EXTERNAL_IF, p + 1,IF_NAMESIZE);
            traceit("EXTERNAL_IF=[%s]\n",EXTERNAL_IF);
            params ++;
         }
      }
      else
      if (strcmp(inbuf,"G2_EXTERNAL_PORT") == 0)
      {
         G2_EXTERNAL_PORT = atoi(p + 1);
         traceit("G2_EXTERNAL_PORT=[%d]\n",G2_EXTERNAL_PORT);
         params ++;
      }
      else
      if (strcmp(inbuf,"INTERNAL_IF") == 0)
      {
         ptr = strchr(p + 1, ' ');
         if (ptr)
            *ptr = '\0';

         if (strlen(p + 1) < 1)
            traceit("INTERNAL_IF value [%s] invalid\n", p + 1);
         else
         {
            memset(INTERNAL_IF, '\0', sizeof(INTERNAL_IF));
            strncpy(INTERNAL_IF, p + 1,IF_NAMESIZE);
            traceit("INTERNAL_IF=[%s]\n",INTERNAL_IF);
            params ++;
         }
      }
      else
      if (strcmp(inbuf,"G2_INTERNAL_PORT") == 0)
      {
         G2_INTERNAL_PORT = atoi(p + 1);
         traceit("G2_INTERNAL_PORT=[%d]\n",G2_INTERNAL_PORT);
         G2_INTERNAL_PORT = htons(G2_INTERNAL_PORT);
         params ++;
      }
      else
      if (strcmp(inbuf,"RP2C_PORT") == 0)
      {
         RP2C_PORT = atoi(p + 1);
         traceit("RP2C_PORT=[%d]\n",RP2C_PORT);
         RP2C_PORT = htons(RP2C_PORT);
         params ++;
      }
      else
      if (strcmp(inbuf,"RMT_XRF_PORT") == 0)
      {
         RMT_XRF_PORT = atoi(p + 1);
         traceit("RMT_XRF_PORT=[%d]\n",RMT_XRF_PORT);
         params ++;
      }
      else
      if (strcmp(inbuf,"RMT_DCS_PORT") == 0)
      {
         RMT_DCS_PORT = atoi(p + 1);
         traceit("RMT_DCS_PORT=[%d]\n",RMT_DCS_PORT);
         params ++;
      }
      else
      if (strcmp(inbuf,"RMT_REF_PORT") == 0)
      {
         RMT_REF_PORT = atoi(p + 1);
         traceit("RMT_REF_PORT=[%d]\n",RMT_REF_PORT);
         params ++;
      }
      else
      if (strcmp(inbuf,"COMMAND_PORT") == 0)
      {
         COMMAND_PORT = atoi(p + 1);
         traceit("COMMAND_PORT=[%d]\n",COMMAND_PORT);
         params ++;
      }
      else
      if (strcmp(inbuf,"QSO_DETAILS") == 0)
      {
         if (*(p + 1) == 'Y')
            QSO_DETAILS = true;
         else
            QSO_DETAILS = false;
         traceit("QSO_DETAILS=[%c]\n", *(p + 1));
         params ++;
      }
      else
      if (strcmp(inbuf,"GWYS") == 0)
      {
         memset(GWYS,  '\0', sizeof(GWYS));
         strncpy(GWYS, p + 1,FILENAME_MAX);
         traceit("GWYS=[%s]\n", GWYS);
         params ++;
      }
      else
      if (strcmp(inbuf,"VALID_CALLSIGNS") == 0)
      {
         memset(VALID_CALLSIGNS,  '\0', sizeof(VALID_CALLSIGNS));
         strncpy(VALID_CALLSIGNS, p + 1,FILENAME_MAX);
         traceit("VALID_CALLSIGNS=[%s]\n", VALID_CALLSIGNS);
         params ++;
      }
      else
      if (strcmp(inbuf,"DTMF_DIR") == 0)
      {
         memset(DTMF_DIR, '\0', sizeof(DTMF_DIR));
         strncpy(DTMF_DIR, p + 1, FILENAME_MAX);
         traceit("DTMF_DIR=[%s]\n", DTMF_DIR);
         params ++;
      }
      else
      if (strcmp(inbuf,"STATUS_FILE") == 0)
      {
         memset(STATUS_FILE, '\0', sizeof(STATUS_FILE));
         strncpy(STATUS_FILE, p + 1,FILENAME_MAX);
         traceit("STATUS_FILE=[%s]\n",STATUS_FILE);
         params ++;
      }
      else
      if (strcmp(inbuf,"ANNOUNCE") == 0)
      {
         if (*(p + 1) == 'Y')
            ANNOUNCE = true;
         else
            ANNOUNCE = false;
         traceit("ANNOUNCE=[%c]\n", *(p + 1));
         params ++;
      }
      else
      if (strcmp(inbuf,"ANNOUNCE_DIR") == 0)
      {
         memset(ANNOUNCE_DIR, '\0', sizeof(ANNOUNCE_DIR));
         strncpy(ANNOUNCE_DIR, p + 1, FILENAME_MAX);
         traceit("ANNOUNCE_DIR=[%s]\n", ANNOUNCE_DIR);
         params ++;
      }
      else
      if (strcmp(inbuf,"RPTR_ACK") == 0)
      {
         if (*(p + 1) == 'Y')
            RPTR_ACK = true;
         else
            RPTR_ACK = false;
         traceit("RPTR_ACK=[%c]\n", *(p + 1));
         params ++;
      }
      else
      if (strcmp(inbuf,"DELAY_BETWEEN") == 0)
      {
         DELAY_BETWEEN = atoi(p + 1);
         if (DELAY_BETWEEN <= 0)
            DELAY_BETWEEN = 20;
         traceit("DELAY_BETWEEN=[%d]\n",DELAY_BETWEEN);
         params ++;
      }
      else
      if (strcmp(inbuf,"DELAY_BEFORE") == 0)
      {
         DELAY_BEFORE = atoi(p + 1);
         if (DELAY_BEFORE <= 0)
            DELAY_BEFORE = 1;
         traceit("DELAY_BEFORE=[%d]\n",DELAY_BEFORE);
         params ++;
      }
      else
      if (strcmp(inbuf,"LINK_AT_STARTUP_A") == 0)
      {
         memset(LINK_AT_STARTUP_A, '\0', sizeof(LINK_AT_STARTUP_A));
         strncpy(LINK_AT_STARTUP_A, p + 1, CALL_SIZE);
         traceit("LINK_AT_STARTUP_A=[%s]\n", LINK_AT_STARTUP_A);
         params ++;
      }
      if (strcmp(inbuf,"LINK_AT_STARTUP_B") == 0)
      {
         memset(LINK_AT_STARTUP_B, '\0', sizeof(LINK_AT_STARTUP_B));
         strncpy(LINK_AT_STARTUP_B, p + 1, CALL_SIZE);
         traceit("LINK_AT_STARTUP_B=[%s]\n", LINK_AT_STARTUP_B);
         params ++;
      }
      if (strcmp(inbuf,"LINK_AT_STARTUP_C") == 0)
      {
         memset(LINK_AT_STARTUP_C, '\0', sizeof(LINK_AT_STARTUP_C));
         strncpy(LINK_AT_STARTUP_C, p + 1, CALL_SIZE);
         traceit("LINK_AT_STARTUP_C=[%s]\n", LINK_AT_STARTUP_C);
         params ++;
      }
      else
      if (strcmp(inbuf,"MAX_DONGLES") == 0)
      {
         MAX_DONGLES = atoi(p + 1);
         traceit("MAX_DONGLES=[%d]\n",MAX_DONGLES);
         SAVED_MAX_DONGLES = MAX_DONGLES;
         params ++;
      }
      else
      /* if (strcmp(inbuf,"REPORTS") == 0)
      {
         memset(REPORTS, 0, sizeof(REPORTS));
         strncpy(REPORTS, p + 1, MAXHOSTNAMELEN);
         traceit("REPORTS=[%s]\n", REPORTS);
         params ++;
      }
      else
      if (strcmp(inbuf,"AUTH0") == 0)
      {
         memset(AUTH0, 0, sizeof(AUTH0));
         strncpy(AUTH0, p + 1, MAXHOSTNAMELEN);
         traceit("AUTH0=[%s]\n", AUTH0);
         params ++;
      }
      else
      if (strcmp(inbuf,"AUTH1") == 0)
      {
         memset(AUTH1, 0, sizeof(AUTH1));
         strncpy(AUTH1, p + 1, MAXHOSTNAMELEN);
         traceit("AUTH1=[%s]\n", AUTH1);
         params ++;
      }
      else
      if (strcmp(inbuf,"AUTH2") == 0)
      {
         memset(AUTH2, 0, sizeof(AUTH2));
         strncpy(AUTH2, p + 1, MAXHOSTNAMELEN);
         traceit("AUTH2=[%s]\n", AUTH2);
         params ++;
      }
      else
      if (strcmp(inbuf,"ECHOTEST_DIR") == 0)
      {
         memset(ECHOTEST_DIR, '\0', sizeof(ECHOTEST_DIR));
         strncpy(ECHOTEST_DIR, p + 1, FILENAME_MAX);
         traceit("ECHOTEST_DIR=[%s]\n", ECHOTEST_DIR);
         params ++;
      }
      else
      if (strcmp(inbuf,"ECHOTEST_REC_TIMEOUT") == 0)
      {
         ECHOTEST_REC_TIMEOUT = atoi(p + 1);
         if (ECHOTEST_REC_TIMEOUT <= 0)
            ECHOTEST_REC_TIMEOUT = 1;
         traceit("ECHOTEST_REC_TIMEOUT=[%d]\n", ECHOTEST_REC_TIMEOUT);
         params ++;
      }
      
      else

      */

      if (strcmp(inbuf,"RF_INACTIVITY_TIMER_A") == 0)
      {
         RF_INACTIVITY_TIMER[0] = atol(p + 1);
         if (RF_INACTIVITY_TIMER[0] < 0)
            RF_INACTIVITY_TIMER[0] = 10;
         traceit("RF_INACTIVITY_TIMER_A=[%ld]\n",RF_INACTIVITY_TIMER[0]);
         RF_INACTIVITY_TIMER[0] = RF_INACTIVITY_TIMER[0] * 60;
         params ++;
      }
      else
      if (strcmp(inbuf,"RF_INACTIVITY_TIMER_B") == 0)
      {
         RF_INACTIVITY_TIMER[1] = atol(p + 1);
         if (RF_INACTIVITY_TIMER[1] < 0)
            RF_INACTIVITY_TIMER[1] = 10;
         traceit("RF_INACTIVITY_TIMER_B=[%ld]\n",RF_INACTIVITY_TIMER[1]);
         RF_INACTIVITY_TIMER[1] = RF_INACTIVITY_TIMER[1] * 60;
         params ++;
      }
      else
      if (strcmp(inbuf,"RF_INACTIVITY_TIMER_C") == 0)
      {
         RF_INACTIVITY_TIMER[2] = atol(p + 1);
         if (RF_INACTIVITY_TIMER[2] < 0)
            RF_INACTIVITY_TIMER[2] = 10;
         traceit("RF_INACTIVITY_TIMER_C=[%ld]\n",RF_INACTIVITY_TIMER[2]);
         RF_INACTIVITY_TIMER[2] = RF_INACTIVITY_TIMER[2] * 60;
         params ++;
      }
      else
      if (strcmp(inbuf,"RF_FLAGS_DIR") == 0)
      {
         memset(RF_FLAGS_DIR, '\0', sizeof(RF_FLAGS_DIR));
         strncpy(RF_FLAGS_DIR, p + 1, FILENAME_MAX);
         traceit("RF_FLAGS_DIR=[%s]\n", RF_FLAGS_DIR);
         params ++;         
      }


   }
   fclose(cnf);

   if (params != valid_params)
   {
      traceit("Configuration file %s invalid\n",cfgFile);
      return false;
   }

   return true;
}

/* create our server */
static bool srv_open()
{
   struct sockaddr_in sin;
   short i;
   struct ifreq ifr;
   struct sockaddr_in *paddr;
   int external_raw_sock = -1;

   external_raw_sock = socket(PF_PACKET, SOCK_DGRAM, htons(ETH_P_IP));
   if (external_raw_sock == -1)
   {
      traceit("Failed to create external raw socket, errno=%d\n", errno);
      return false;
   }
   memset(&ifr, '\0', sizeof(ifr));
   strncpy((char *)ifr.ifr_name, EXTERNAL_IF, IFNAMSIZ);
   if ((ioctl(external_raw_sock, SIOCGIFADDR, &ifr)) == -1)
   {
      traceit("SIOCGIFADDR failed on EXTERNAL_IF %s, errno=%d\n",EXTERNAL_IF,errno);
      close(external_raw_sock);
      return false;
   }
   close(external_raw_sock);
   paddr = (struct sockaddr_in *)&(ifr.ifr_addr);
   memset(LISTEN_IP, '\0', sizeof(LISTEN_IP));
   strncpy(LISTEN_IP, inet_ntoa(paddr->sin_addr), IP_SIZE);
   traceit("EXTERNAL_IF %s has local IP %s\n", EXTERNAL_IF, LISTEN_IP);

   /* create our XRF gateway socket */ 
   xrf_g2_sock = socket(PF_INET,SOCK_DGRAM,0);
   if (xrf_g2_sock == -1)
   {
      traceit("Failed to create gateway socket for XRF,errno=%d\n",errno);
      return false;
   }
   fcntl(xrf_g2_sock,F_SETFL,O_NONBLOCK);
   memset(&sin,0,sizeof(struct sockaddr_in));
   sin.sin_family = AF_INET;
   sin.sin_addr.s_addr = inet_addr(LISTEN_IP);
   sin.sin_port = htons(RMT_XRF_PORT);
   if (bind(xrf_g2_sock,(struct sockaddr *)&sin,sizeof(struct sockaddr_in)) != 0)
   {
      traceit("Failed to bind gateway socket on port %d for XRF, errno=%d\n",
              RMT_XRF_PORT ,errno);
      close(xrf_g2_sock);
      xrf_g2_sock = -1;
      return false;
   }

   /* create the dcs socket */
   dcs_g2_sock = socket(PF_INET,SOCK_DGRAM,0);
   if (dcs_g2_sock == -1)
   {
      traceit("Failed to create gateway socket for DCS,errno=%d\n",errno);
      close(xrf_g2_sock);
      xrf_g2_sock = -1;
      return false;
   }
   fcntl(dcs_g2_sock,F_SETFL,O_NONBLOCK);

   /* socket for REF */
   ref_g2_sock = socket(PF_INET,SOCK_DGRAM,0);
   if (ref_g2_sock == -1)
   {
      traceit("Failed to create gateway socket for REF, errno=%d\n",errno);
      close(dcs_g2_sock);
      dcs_g2_sock = -1;
      close(xrf_g2_sock);
      xrf_g2_sock = -1;
      return false;
   }
   fcntl(ref_g2_sock,F_SETFL,O_NONBLOCK);

   sin.sin_family = AF_INET;
   sin.sin_addr.s_addr = inet_addr(LISTEN_IP);
   sin.sin_port = htons(RMT_REF_PORT);
   if (bind(ref_g2_sock,(struct sockaddr *)&sin,sizeof(struct sockaddr_in)) != 0)
   {
      traceit("Failed to bind gateway socket on port %d for REF, errno=%d\n",
              RMT_REF_PORT ,errno);
      close(dcs_g2_sock);
      dcs_g2_sock = -1;
      close(xrf_g2_sock);
      xrf_g2_sock = -1;
      close(ref_g2_sock);
      ref_g2_sock = -1;
      return false;
   }

   /* create our repeater socket */
   rptr_sock = socket(PF_PACKET, SOCK_DGRAM, htons(ETH_P_IP));
   if (rptr_sock == -1)
   {
      traceit("Failed to create repeater socket,errno=%d\n",errno);
      close(dcs_g2_sock);
      dcs_g2_sock = -1;
      close(xrf_g2_sock);
      xrf_g2_sock = -1;
      close(ref_g2_sock);
      ref_g2_sock = -1;
      return false;
   }
   memset(&ifr, '\0', sizeof(ifr));
   strncpy((char *)ifr.ifr_name, INTERNAL_IF, IFNAMSIZ);
   if ((ioctl(rptr_sock, SIOCGIFADDR, &ifr)) == -1)
   {
      traceit("SIOCGIFADDR failed on INTERNAL_IF %s, errno=%d\n",INTERNAL_IF,errno);
      close(dcs_g2_sock);
      dcs_g2_sock = -1;
      close(rptr_sock);
      rptr_sock = -1;
      close(xrf_g2_sock);
      xrf_g2_sock = -1;
      close(ref_g2_sock);
      ref_g2_sock = -1;
      return false;
   }
   paddr = (struct sockaddr_in*)&(ifr.ifr_addr);
   traceit("INTERNAL_IF %s has local IP %s\n",
           INTERNAL_IF, inet_ntoa(paddr->sin_addr));

   internal_daddr = paddr->sin_addr.s_addr;

   memset(&sll, '\0', sizeof(sll));
   sll.sll_family = AF_PACKET;
   sll.sll_ifindex = if_nametoindex(INTERNAL_IF);
   sll.sll_protocol = htons(ETH_P_ALL);
   if ((bind(rptr_sock, (struct sockaddr *)&sll, sizeof(sll)))== -1)
   {
      traceit("Failed to bind repeater socket on %s, errno=%d\n",
              INTERNAL_IF,errno);
      close(dcs_g2_sock);
      dcs_g2_sock = -1;
      close(rptr_sock);
      rptr_sock = -1;
      close(xrf_g2_sock);
      xrf_g2_sock = -1;
      close(ref_g2_sock);
      ref_g2_sock = -1;
      return false;
   }
   fcntl(rptr_sock,F_SETFL,O_NONBLOCK);

   /* open the command port */
   cmd_sock = socket(PF_INET,SOCK_DGRAM,0);
   if (cmd_sock == -1)
   {
      traceit("Failed to create cmd socket,errno=%d\n",errno);
      close(dcs_g2_sock);
      dcs_g2_sock = -1;
      close(rptr_sock);
      rptr_sock = -1;
      close(xrf_g2_sock);
      xrf_g2_sock = -1;
      close(ref_g2_sock);
      ref_g2_sock = -1;
      return false;
   }
   memset(&sin,0,sizeof(struct sockaddr_in));
   sin.sin_family = AF_INET;
   sin.sin_port = htons(COMMAND_PORT);
   sin.sin_addr.s_addr = inet_addr("0.0.0.0");

   if (bind(cmd_sock,(struct sockaddr *)&sin,sizeof(struct sockaddr_in)) != 0)
   {
      traceit("Failed to bind cmd socket on port %d, errno=%d\n", COMMAND_PORT, errno);
      close(dcs_g2_sock);
      dcs_g2_sock = -1;
      close(cmd_sock);
      cmd_sock = -1;
      close(rptr_sock);
      rptr_sock = -1;
      close(xrf_g2_sock);
      xrf_g2_sock = -1;
      close(ref_g2_sock);
      ref_g2_sock = -1;
      return false;
   }
   fcntl(cmd_sock,F_SETFL,O_NONBLOCK);

   /* the local G2 external runs on this IP and port */
   memset(&toLocalg2,0,sizeof(struct sockaddr_in));
   toLocalg2.sin_family = AF_INET;
   toLocalg2.sin_addr.s_addr = inet_addr(LISTEN_IP);
   toLocalg2.sin_port = htons(G2_EXTERNAL_PORT);

   /* initialize all remote links */
   for (i = 0; i < 3; i++)
   {
      to_remote_g2[i].type = ' ';
      to_remote_g2[i].to_call[0] = '\0';
      memset(&(to_remote_g2[i].toDst4),0,sizeof(struct sockaddr_in));
      to_remote_g2[i].from_mod = ' ';
      to_remote_g2[i].to_mod = ' ';
      to_remote_g2[i].countdown = 0;
      to_remote_g2[i].is_connected = false;
      to_remote_g2[i].in_streamid[0] = 0x00;
      to_remote_g2[i].in_streamid[1] = 0x00;
      to_remote_g2[i].out_streamid[0] = 0x00;
      to_remote_g2[i].out_streamid[1] = 0x00;
   }
   return true;
}  

/* destroy our server */
static void srv_close()
{
   if (xrf_g2_sock != -1)
   {
      close(xrf_g2_sock);
      traceit("Closed RMT_XRF_PORT\n");
   }

   if (dcs_g2_sock != -1)
   {
      close(dcs_g2_sock);
      traceit("Closed RMT_DCS_PORT\n");
   }

   if (rptr_sock != -1)
   {
      close(rptr_sock);
      traceit("Closed MY_G2_LINK_PORT\n");
   }

   if (ref_g2_sock != -1)
   {
      close(ref_g2_sock);
      traceit("Closed RMT_REF_PORT\n");
   }
   return;
}

static bool resolve_plus()
{
   // bool ok = false;

   /*** REPORTS ***/


/*   memset(&to_reports,0,sizeof(struct sockaddr_in));
   while (keep_running)
   {
      ok = resolve_rmt(REPORTS, SOCK_DGRAM, &to_reports);
      if (!ok)
      {
         traceit("Could not resolve host [%s] to IP, will try again in 10 seconds...\n", REPORTS);
         sleep(10);
      }
      else
         break;
   }
   to_reports.sin_family = AF_INET;
   to_reports.sin_port = htons(20002);
   traceit("REPORTS resolved to [%s]\n", inet_ntoa(to_reports.sin_addr));
*/

   /*** AUTH0 ***/
/*   memset(&to_auth0,0,sizeof(struct sockaddr_in));
   while (keep_running)
   {
      ok = resolve_rmt(AUTH0, SOCK_DGRAM, &to_auth0);
      if (!ok)
      {
         traceit("Could not resolve host [%s] to IP, will try again in 10 seconds...\n", AUTH0);
         sleep(10);
      }
      else
         break;
   }
   to_auth0.sin_family = AF_INET;
   to_auth0.sin_port = htons(20001);
   traceit("AUTH0 resolved to [%s]\n", inet_ntoa(to_auth0.sin_addr));
*/

   /*** AUTH1 ***/

/*   memset(&to_auth1,0,sizeof(struct sockaddr_in));
   while (keep_running)
   {
      ok = resolve_rmt(AUTH1, SOCK_DGRAM, &to_auth1);
      if (!ok)
      {
         traceit("Could not resolve host [%s] to IP, will try again in 10 seconds...\n", AUTH1);
         sleep(10);
      }
      else
         break;
   }
   to_auth1.sin_family = AF_INET;
   to_auth1.sin_port = htons(20001);
   traceit("AUTH1 resolved to [%s]\n", inet_ntoa(to_auth1.sin_addr));

*/

   /*** AUTH2 ***/

/*   memset(&to_auth2,0,sizeof(struct sockaddr_in));
   while (keep_running)
   {
      ok = resolve_rmt(AUTH2, SOCK_DGRAM, &to_auth2);
      if (!ok)
      {
         traceit("Could not resolve host [%s] to IP, will try again in 10 seconds...\n", AUTH2);
         sleep(10);
      }
      else
         break;
   }
   to_auth2.sin_family = AF_INET;
   to_auth2.sin_port = htons(20001);
   traceit("AUTH2 resolved to [%s]\n", inet_ntoa(to_auth2.sin_addr));
*/
   return true;

}

/* find the repeater IP by callsign and link to it */
static void g2link(char from_mod, char *call, char to_mod)
{
   short i,j, counter;

   char host[MAXHOSTNAMELEN + 1];
   char port_s[5 + 1];
   int port_i;

   /* host + space + port + NULL */
   char payload[MAXHOSTNAMELEN + 1 + 5 + 1];
   char *p = NULL;

   gwy_list_type::iterator gwy_pos;
   char link_request[519];

   bool ok = false;

   memset(link_request, 0, sizeof(link_request));

   host[0] = '\0';
   port_s[0] = '\0';
   payload[0] = '\0';

   if (from_mod == 'A')
      i = 0;
   else
   if (from_mod == 'B')
      i = 1;
   else
   if (from_mod == 'C')
      i = 2;
   else
   {
       traceit("from_mod %c invalid\n", from_mod);
       return;
   }

   //v3.18 - go and check to make sure that the local module is not being used by dplus (i.e., is not connected to a dplus host

   if (!df_check(from_mod))
   {
      traceit("Module is presently being used by dplus - cannot link to another host\n");
      return;
   }


   /* XRF or REF have only A,B,C,D,E modules */
   if ((memcmp(call, "XRF", 3) == 0) ||
       (memcmp(call, "REF", 3) == 0))
   {
      if ((to_mod != 'A') && (to_mod != 'B') && (to_mod != 'C') &&
          (to_mod != 'D') && (to_mod != 'E'))
      {
         traceit("to_mod %c invalid\n", to_mod);
         return;
      }

// v3.18

      if ((memcmp(call, "REF", 3) == 0))
      {
        traceit("REF Linking is not permitted\n");
        return;
      }
   }

   memset(&to_remote_g2[i], 0, sizeof(to_remote_g2[i]));

   strcpy(to_remote_g2[i].to_call, call);
   to_remote_g2[i].to_mod = to_mod; 

   /* DCS will not allow multilinking */
   if (memcmp(call, "DCS", 3) == 0)
   {
      for (counter = 0; counter < 3; counter++)
      {
         if (counter != i)
         {
            if ( (to_remote_g2[counter].to_call[0] != '\0') &&
                 (strcmp(to_remote_g2[counter].to_call,to_remote_g2[i].to_call) == 0) &&
                 (to_remote_g2[counter].to_mod == to_remote_g2[i].to_mod) )
               break;
         }
      }
      to_remote_g2[i].to_call[0] = '\0';
      to_remote_g2[i].to_mod = ' ';

      if (counter < 3)
      {
         traceit("Another mod(%c) is already linked to %s %c\n",
                 to_remote_g2[counter].from_mod,
                 to_remote_g2[counter].to_call,
                 to_remote_g2[counter].to_mod);

         return;
      }
   }

   gwy_pos = gwy_list.find(call);
   if (gwy_pos == gwy_list.end())
   {
      traceit("%s not found in gwy list\n", call);
      return;
   }

   strcpy(payload, gwy_pos->second.c_str());
   
   /* extract host and port */
   p = strchr(payload, ' ');
   if (!p)
   {
      traceit("Invalid payload [%s] for call [%s]\n", payload, call);
      return;
   }
   *p = '\0';

   strcpy(host, payload);
   strcpy(port_s, p + 1);
   port_i = atoi(port_s);

   if (host[0] != '\0')
   {
      ok = resolve_rmt(host, SOCK_DGRAM, &(to_remote_g2[i].toDst4));
      if (!ok)
      {
         traceit("Call %s is host %s but could not resolve to IP\n",
                 call, host);
         memset(&to_remote_g2[i], 0, sizeof(to_remote_g2[i]));
         return;
      }

      if (port_i == RMT_XRF_PORT)
         to_remote_g2[i].type = 'x';
      else
      if (port_i == RMT_REF_PORT)
         to_remote_g2[i].type = 'p';
      else
      if (port_i == RMT_DCS_PORT)
         to_remote_g2[i].type = 'd';
      else
      {
         traceit("Host [%s] has INVALID port [%d]\n", host, port_i);
         memset(&to_remote_g2[i], 0, sizeof(to_remote_g2[i]));
         return;
      }
      strcpy(to_remote_g2[i].to_call, call);
      to_remote_g2[i].toDst4.sin_family = AF_INET;
      to_remote_g2[i].toDst4.sin_port = htons(port_i);
      to_remote_g2[i].from_mod = from_mod;
      to_remote_g2[i].to_mod = to_mod;
      to_remote_g2[i].countdown = TIMEOUT;
      to_remote_g2[i].is_connected = false;
      to_remote_g2[i].in_streamid[0] = 0x00; 
      to_remote_g2[i].in_streamid[1] = 0x00;

// v3.18

      df_block(tolower(from_mod));
//

      /* is it XRF? */
      if (port_i == RMT_XRF_PORT)
      {
         strcpy(link_request, OWNER);
         link_request[8] = from_mod;
         link_request[9] = to_mod;
         link_request[10] = '\0';

         traceit("sending link request(dextra) from mod %c to link with: [%s] mod %c [%s]\n",
              to_remote_g2[i].from_mod,
              to_remote_g2[i].to_call, to_remote_g2[i].to_mod, payload);

         for (j = 0; j < 5; j++)
            sendto(xrf_g2_sock,link_request, CALL_SIZE + 3,0,
                (struct sockaddr *)&(to_remote_g2[i].toDst4),
                sizeof(to_remote_g2[i].toDst4));
      }
      else
      if (port_i == RMT_DCS_PORT)
      {
         strcpy(link_request, OWNER);
         link_request[8] = from_mod;
         link_request[9] = to_mod;
         link_request[10] = '\0';
         memcpy(link_request + 11, to_remote_g2[i].to_call, 8);
         strcpy(link_request + 19, G2_html);

         traceit("sending link request from mod %c to link with: [%s] mod %c [%s]\n",
              to_remote_g2[i].from_mod,
              to_remote_g2[i].to_call, to_remote_g2[i].to_mod, payload);

         // VA3UV - Changed login from 5 to 1

         for (j = 0; j < 1; j++)
            sendto(dcs_g2_sock,link_request, 519,0,
                (struct sockaddr *)&(to_remote_g2[i].toDst4),
                sizeof(to_remote_g2[i].toDst4));
      }
      else
      {
         traceit("sending link request(plus) from mod %c to: [%s] mod %c [%s]\n",
                 to_remote_g2[i].from_mod,
                 to_remote_g2[i].to_call, to_remote_g2[i].to_mod, payload);
         link_plus(i);
      }
   }
   return;
}

static void link_plus(short int i)
{
   unsigned char buf[32];
   short int j;
   unsigned char code = 0x00;
   //static bool auth0 = true;

   /*** 13 bytes to request a link ***/
   buf[0] = 0x0d;
   buf[1] = 0x00;
   buf[2] = 0x18;

   /* local module */
   if (to_remote_g2[i].from_mod == 'A')
      code = code | 0x00;
   else
   if (to_remote_g2[i].from_mod == 'B')
      code = code | 0x10;
   else
   if (to_remote_g2[i].from_mod == 'C')
      code = code | 0x20;

   /* remote module */
   if (to_remote_g2[i].to_mod == 'A')
      code = code | 0x00;
   else
   if (to_remote_g2[i].to_mod == 'B')
      code = code | 0x01;
   else
   if (to_remote_g2[i].to_mod == 'C')
      code = code | 0x02;
   else
   if (to_remote_g2[i].to_mod == 'D')
      code = code | 0x03;
   else
   if (to_remote_g2[i].to_mod == 'E')
      code = code | 0x04;   
  
   buf[3] = code;
   buf[4] = 0x03;

   /* copy the seed */
   /*** use the one that is NOT zero ***/
   //if (memcmp(rep_from_auth0_ok + 5, "\000\000\000\000", 4) == 0)
   //   auth0 = false;

   //if (memcmp(rep_from_auth1_ok + 5, "\000\000\000\000", 4) == 0)
   //   auth0 = true;

   //if (auth0)
   /* {
      memcpy(buf + 5,  rep_from_auth0_ok + 5, 4);
      traceit("Using auth0\n");
   }
   else
   {
      memcpy(buf + 5,  rep_from_auth1_ok + 5, 4);
      traceit("Using auth1\n");
   } */

   //auth0 = !auth0;

   /* identify version */
   memcpy(buf + 9, "22j ", 4);

   traceit("plus link request: [%02x%02x %02x%02x %02x%02x %02x%02x %02x%02x %02x%02x %02x]\n",
           buf[0],buf[1],buf[2],buf[3],buf[4],buf[5],buf[6],buf[7],buf[8],buf[9],
           buf[10],buf[11],buf[12]);

   if (memcmp(buf + 5, "\000\000\000\000", 4) == 0)
   {
      traceit("Seed is stil 00, will not link yet\n");

      to_remote_g2[i].type = ' ';
      to_remote_g2[i].to_call[0] = '\0';
      memset(&(to_remote_g2[i].toDst4),0,sizeof(struct sockaddr_in));
      to_remote_g2[i].from_mod = ' ';
      to_remote_g2[i].to_mod = ' ';
      to_remote_g2[i].countdown = 0;
      to_remote_g2[i].is_connected = false;
      to_remote_g2[i].in_streamid[0] = 0x00;
      to_remote_g2[i].in_streamid[1] = 0x00;

      return;
   }
   
   for (j = 0; j < 3; j++)
      sendto(ref_g2_sock, buf, 13 ,0,
             (struct sockaddr *)&(to_remote_g2[i].toDst4),
             sizeof(to_remote_g2[i].toDst4));

   return;
}


/* signal catching function */
static void sigCatch(int signum)
{
   /* do NOT do any serious work here */
   if ((signum == SIGTERM) || (signum == SIGINT))
      keep_running = false;
   return;
}

static void runit()
{
   socklen_t fromlen;
   int recvlen;
   int recvlen2;
   short i,j,k,i_tmp;
   char temp_repeater[CALL_SIZE + 1];
   time_t tnow = 0, hb = 0;
   int rc = 0;

   struct iphdr *ip_hdr;
   struct udphdr *udp_hdr;

   char *p = NULL;

   char notify_msg[64];
   char *space_p = 0;
   char linked_remote_system[CALL_SIZE + 1];
   char unlink_request[CALL_SIZE + 3];

   // v3.18 - no longer used char system_cmd[FILENAME_MAX + 1];
   int max_nfds = 0;

   char tmp1[CALL_SIZE + 1];
   char tmp2[36]; // 8 for rpt1 + 24 for time_t in string format
   dt_lh_type::iterator dt_lh_pos;
   dt_lh_type::reverse_iterator r_dt_lh_pos;

   gwy_list_type::iterator gwy_pos;
   ip_list_type::iterator ip_pos;

   char call[CALL_SIZE + 1];
   char ip[IP_SIZE + 1];
   inbound *inbound_ptr;
   inbound_type::iterator pos;
   pair<inbound_type::iterator,bool> insert_pair;
   bool found = false;
   set<string>::iterator it;

   unsigned char dplus_ack[5];
   char temp[32];
   struct timezone tz;

   int ber_data[3];
   int ber_errs;

   char cmd_2_dcs[23];
   unsigned char dcs_seq[3] = { 0x00, 0x00, 0x00 };
   struct {
     char mycall[9];
     char sfx[5];
     unsigned int dcs_rptr_seq;
   } rptr_2_dcs[3] = { {"        ", "    ", 0},
                       {"        ", "    ", 0},
                       {"        ", "    ", 0} };
   struct {
     char mycall[9];
     char sfx[5];
     unsigned int dcs_rptr_seq;
   } ref_2_dcs[3] = { {"        ", "    ", 0},
                      {"        ", "    ", 0},
                      {"        ", "    ", 0} };
   struct {
     char mycall[9];
     char sfx[5];
     unsigned int dcs_rptr_seq;
   } xrf_2_dcs[3] = { {"        ", "    ", 0},
                      {"        ", "    ", 0},
                      {"        ", "    ", 0} };

   u_int16_t streamid_raw;
   char source_stn[9];
   char tempfile[FILENAME_MAX + 1];

//v3.18

   char df_b[FILENAME_MAX + 1];
//
   memset(notify_msg, '\0', sizeof(notify_msg));
   time(&hb);

   dstar_dv_init();

   if (xrf_g2_sock > max_nfds)
      max_nfds = xrf_g2_sock;
   if (ref_g2_sock > max_nfds)
      max_nfds = ref_g2_sock;
   if (rptr_sock > max_nfds)
      max_nfds = rptr_sock;
   if (cmd_sock > max_nfds)
      max_nfds = cmd_sock;
   if (dcs_g2_sock > max_nfds)
      max_nfds = dcs_g2_sock;

   traceit("xrf=%d, dcs=%d, ref=%d, rptr=%d, cmd=%d, MAX+1=%d\n", 
            xrf_g2_sock, dcs_g2_sock, ref_g2_sock, rptr_sock, cmd_sock, max_nfds + 1);

   if (strlen(LINK_AT_STARTUP_A) >= 8)
   {
      if ((LINK_AT_STARTUP_A[0]) == 'A') 
      {
         memset(temp_repeater, ' ', CALL_SIZE);
         memcpy(temp_repeater, LINK_AT_STARTUP_A + 1, 6);
         temp_repeater[CALL_SIZE] = '\0';
         g2link(LINK_AT_STARTUP_A[0], temp_repeater, LINK_AT_STARTUP_A[7]);
      }
   }

   if (strlen(LINK_AT_STARTUP_B) >= 8)
   {
      if ((LINK_AT_STARTUP_B[0]) == 'B')
      {
         memset(temp_repeater, ' ', CALL_SIZE);        
         memcpy(temp_repeater, LINK_AT_STARTUP_B + 1, 6);         
         temp_repeater[CALL_SIZE] = '\0';
         g2link(LINK_AT_STARTUP_B[0], temp_repeater, LINK_AT_STARTUP_B[7]);
      }   
   }   
   if (strlen(LINK_AT_STARTUP_C) >= 8)
   {
      if ((LINK_AT_STARTUP_C[0]) == 'C')
      {
         memset(temp_repeater, ' ', CALL_SIZE);        
         memcpy(temp_repeater, LINK_AT_STARTUP_C + 1, 6);         
         temp_repeater[CALL_SIZE] = '\0';
         g2link(LINK_AT_STARTUP_C[0], temp_repeater, LINK_AT_STARTUP_C[7]);
      }   
   }

   
   /*** start ***/
   sm_to_r.codes[0] = 0xbb;
   sm_to_r.codes[1] = 0xc0;
   sm_to_r.codes[2] = 0x10;
   sm_to_r.codes[3] = 0x00;
   memcpy(sm_to_r.version, "dplus 2.2j", 10);
   sm_to_r.sep1 = ':';
   memcpy(sm_to_r.gw, "gwcall=", 7);
   memcpy(sm_to_r.gw + 7, OWNER, 8);
   sm_to_r.sep2 = ':';
   gettimeofday(&tv, &tz);
   sprintf(temp, "time=%010ld.%06ld", tv.tv_sec, tv.tv_usec);
   memcpy(sm_to_r.time, temp, 22);
   sm_to_r.sep3 = ':';
   memcpy(sm_to_r.type, "type=1", 6);
   sm_to_r.sep4 = ':';
   memcpy(sm_to_r.mod,"moduleid=00",11);
   sm_to_r.sep5 = ':';
   memcpy(sm_to_r.streamid, "streamid=0000", 13);
   sm_to_r.sep6 = ':';
   memcpy(sm_to_r.my, "mycall=        ", 15);
   sm_to_r.sep7 = ':';
   memcpy(sm_to_r.sfx, "mysuffix=    ", 13);
   sm_to_r.sep8 = ':';
   memcpy(sm_to_r.yr, "urcall=        ", 15);
   sm_to_r.sep9 = ':';
   memcpy(sm_to_r.rpt1, "rpt1=        ", 13);
   sm_to_r.sep10 = ':';
   memcpy(sm_to_r.rpt2, "rpt2=        ", 13);
   sm_to_r.sep11 = ':';
   memcpy(sm_to_r.msg, "msg=dplus start 22j ", 20);
   sm_to_r.sep12 = ':';
   memcpy(sm_to_r.id, "dplus", 5);
   for (j = 0; j < 2; j++)
      sendto(ref_g2_sock, (char *)&sm_to_r, sizeof(sm_to_r), 0,
             (struct sockaddr *)&to_reports, sizeof(struct sockaddr_in));

   /*** auth ***/
   
/* am_to_a.codes[0] = 0x48;
   am_to_a.codes[1] = 0xa0;
   am_to_a.codes[2] = 0x02;
   am_to_a.codes[3] = 0x00;
   memcpy(am_to_a.auth_type, "auth type=dnsu", 14);
   am_to_a.sep1 = ':';
   memcpy(am_to_a.proto, "proto=1",7);
   am_to_a.sep2 = ':';
   memcpy(am_to_a.prog, "prog=dplus",10);
   am_to_a.sep3 = ':';
   memcpy(am_to_a.version, "progver=2.2j",12);
   am_to_a.sep4 = ':';
   memcpy(am_to_a.gw, "gwcall=", 7);
   memcpy(am_to_a.gw + 7, OWNER, 8);
   am_to_a.sep5 = ':';
   memcpy(am_to_a.id, "auth", 4);
   am_to_a.term = 0x00;
*/

   while (keep_running)
   {
      time(&tnow);
      /*

      // echotest recording timed out?
      for (i = 0; i < 3; i++)
      {
         // echotest recording timed out?
         if (recd[i].last_time != 0)
         {
            if ((tnow - recd[i].last_time) > ECHOTEST_REC_TIMEOUT)
            {
                traceit("Inactivity on echotest recording mod %d, removing stream id=%d,%d\n",
                         i,recd[i].streamid[0], recd[i].streamid[1]);

                recd[i].streamid[0] = 0x00;
                recd[i].streamid[1] = 0x00;
                recd[i].last_time = 0;
                close(recd[i].fd); recd[i].fd = -1;
                // traceit("Closed echotest audio file:[%s]\n", recd[i].file);

                // START: echotest thread setup
                pthread_attr_init(&echo_attr);
                pthread_attr_setdetachstate(&echo_attr, PTHREAD_CREATE_DETACHED);
                rc = pthread_create(&echo_thread, &echo_attr, echotest, (void *)recd[i].file);
                if (rc != 0)
                {
                   traceit("failed to start echotest thread\n");
                   //   when the echotest thread runs, it deletes the file,
                   //   Because the echotest thread did NOT start, we delete the file here
                   
                   unlink(recd[i].file);
                }
                pthread_attr_destroy(&echo_attr);
                // END: echotest thread setup
            }
         }
      }
      */

      /*** every 10 minutes: auth ***/
      /* v3.18 if ((tnow - au_msg_time) > 600)
      {
         // traceit("sending auth msg\n");
         for (j = 0; j < 2; j++)
            sendto(ref_g2_sock, (char *)&am_to_a, sizeof(am_to_a), 0,
                   (struct sockaddr *)&to_auth0, sizeof(struct sockaddr_in));
         for (j = 0; j < 2; j++)
            sendto(ref_g2_sock, (char *)&am_to_a, sizeof(am_to_a), 0,
                   (struct sockaddr *)&to_auth1, sizeof(struct sockaddr_in));
         for (j = 0; j < 2; j++)
            sendto(ref_g2_sock, (char *)&am_to_a, sizeof(am_to_a), 0,
                   (struct sockaddr *)&to_auth2, sizeof(struct sockaddr_in));
         au_msg_time = tnow;
      }

      */

      if ((tnow - hb) > 0)
      {
         /* send heartbeat to connected donglers */
         send_heartbeat();

         /* send heartbeat linked XRF repeaters/reflectors */
         if (to_remote_g2[0].type == 'x')
            sendto(xrf_g2_sock,OWNER, CALL_SIZE + 1, 0,
                   (struct sockaddr *)&(to_remote_g2[0].toDst4),
                   sizeof(to_remote_g2[0].toDst4));

         if ((to_remote_g2[1].type == 'x') &&
             (strcmp(to_remote_g2[1].to_call, to_remote_g2[0].to_call) != 0))
            sendto(xrf_g2_sock,OWNER, CALL_SIZE + 1, 0,
                   (struct sockaddr *)&(to_remote_g2[1].toDst4),
                   sizeof(to_remote_g2[1].toDst4));

         if ((to_remote_g2[2].type == 'x') &&
             (strcmp(to_remote_g2[2].to_call, to_remote_g2[0].to_call) != 0) &&
             (strcmp(to_remote_g2[2].to_call, to_remote_g2[1].to_call) != 0))
            sendto(xrf_g2_sock,OWNER, CALL_SIZE + 1, 0,
                   (struct sockaddr *)&(to_remote_g2[2].toDst4),
                   sizeof(to_remote_g2[2].toDst4));

         /* send heartbeat to linked DCS reflectors */
         if (to_remote_g2[0].type == 'd')
         {
            strcpy(cmd_2_dcs, OWNER); cmd_2_dcs[7] = to_remote_g2[0].from_mod;
            memcpy(cmd_2_dcs + 9, to_remote_g2[0].to_call, 8); cmd_2_dcs[16] = to_remote_g2[0].to_mod;
                   sendto(dcs_g2_sock, cmd_2_dcs, 17, 0,
                   (struct sockaddr *)&(to_remote_g2[0].toDst4),
                   sizeof(to_remote_g2[0].toDst4));
         }
         if (to_remote_g2[1].type == 'd') 
         {
            strcpy(cmd_2_dcs, OWNER); cmd_2_dcs[7] = to_remote_g2[1].from_mod;
            memcpy(cmd_2_dcs + 9, to_remote_g2[1].to_call, 8); cmd_2_dcs[16] = to_remote_g2[1].to_mod;
                   sendto(dcs_g2_sock, cmd_2_dcs, 17, 0,
                   (struct sockaddr *)&(to_remote_g2[1].toDst4),
                   sizeof(to_remote_g2[1].toDst4));
         }
         if (to_remote_g2[2].type == 'd') 
         {
            strcpy(cmd_2_dcs, OWNER); cmd_2_dcs[7] = to_remote_g2[2].from_mod;
            memcpy(cmd_2_dcs + 9, to_remote_g2[2].to_call, 8); cmd_2_dcs[16] = to_remote_g2[2].to_mod;
                   sendto(dcs_g2_sock, cmd_2_dcs, 17, 0,
                   (struct sockaddr *)&(to_remote_g2[2].toDst4),
                   sizeof(to_remote_g2[2].toDst4));
         }

         /* send heartbeat to linked(plus) repeaters or reflectors */
         if (to_remote_g2[0].is_connected &&
             (to_remote_g2[0].type == 'p'))
            sendto(ref_g2_sock, REF_ACK, 3, 0,
                   (struct sockaddr *)&(to_remote_g2[0].toDst4),
                   sizeof(to_remote_g2[0].toDst4));

         if (to_remote_g2[1].is_connected &&
             (to_remote_g2[1].type == 'p') &&
             (strcmp(to_remote_g2[1].to_call, to_remote_g2[0].to_call) != 0))
            sendto(ref_g2_sock, REF_ACK, 3, 0,
                   (struct sockaddr *)&(to_remote_g2[1].toDst4),
                   sizeof(to_remote_g2[1].toDst4));

         if (to_remote_g2[2].is_connected &&
             (to_remote_g2[2].type == 'p') &&
             (strcmp(to_remote_g2[2].to_call, to_remote_g2[0].to_call) != 0) &&
             (strcmp(to_remote_g2[2].to_call, to_remote_g2[1].to_call) != 0))
            sendto(ref_g2_sock, REF_ACK, 3, 0,
                   (struct sockaddr *)&(to_remote_g2[2].toDst4),
                   sizeof(to_remote_g2[2].toDst4));

         for (i = 0; i < 3; i++)
         {
         i_tmp=i;
            if (to_remote_g2[i].to_call[0] != '\0')
            {
               if (to_remote_g2[i].countdown >= 0)
                  to_remote_g2[i].countdown--;

               if (to_remote_g2[i].countdown < 0)
               {
                  /* maybe remote system has changed IP */
                  traceit("Unlinked from [%s] mod %c, TIMEOUT...\n",
                        to_remote_g2[i].to_call, to_remote_g2[i].to_mod);

                  sprintf(notify_msg, "%c_unlinked.dat_UNLINKED_TIMEOUT", to_remote_g2[i].from_mod);
                  audio_notify(notify_msg);

                  //v3.18

                  sprintf(df_b, "/dstar/tmp/blocklinking-%c", tolower(to_remote_g2[i].from_mod));
                  unlink(df_b);

                  to_remote_g2[i].type = ' ';
                  to_remote_g2[i].to_call[0] = '\0';
                  memset(&(to_remote_g2[i].toDst4),0,sizeof(struct sockaddr_in));
                  to_remote_g2[i].from_mod = ' ';
                  to_remote_g2[i].to_mod = ' ';
                  to_remote_g2[i].countdown = 0;
                  to_remote_g2[i].is_connected = false;
                  to_remote_g2[i].in_streamid[0] = 0x00;
                  to_remote_g2[i].in_streamid[1] = 0x00;

                  print_status_file();

               }
            }

            // VA3UV - v 3.13 here....
            //         v3.14 mods - added separate temp_buff_a|b|c arrays to check to see if each module is linked to the default / LINK_AT_STARTUP dest'n
            // check for RF inactivity

            // build an array called 'test' which contains what we are linked to - e.g., BXRF005  B tells us that our module B is linked to XRF005 B

            memset(test, '\0', sizeof test);
            memset(temp_buff, '\0', sizeof temp_buff); //v3.17

            my_module[0]=to_remote_g2[i].from_mod;
            my_module[1]='\0';

            dest_mod[0]=to_remote_g2[i].to_mod;
            dest_mod[1]='\0';

            strcpy(test, my_module);
            strcat(test, to_remote_g2[i].to_call);
            strcat(test, dest_mod);
            strcat(test, " "); 
            
            uv_count_a=0;
            uv_count_b=0;

            do
            {
              if (test[uv_count_b] != ' ')
                temp_buff[uv_count_a] = test[uv_count_b];
              else
                uv_count_a--;

            uv_count_a++;
            uv_count_b++;
    
            }while(uv_count_b < 10);

            temp_buff[uv_count_a + 1] = '\0';
            

            /* v3.15 mods here
               check to see if the LINK_AT_STARTUP module has any spaces in it - i.e., if the callsign is less than 6 characters
               if so, we pack it into a new variable removing the spaces
            */

            uv_count_a=0;
            uv_count_b=0;

            do
            {
              if (LINK_AT_STARTUP_A[uv_count_b] != ' ')
                LINK_AT_STARTUP_A_TMP[uv_count_a] = LINK_AT_STARTUP_A[uv_count_b];
              else
                uv_count_a--;

            uv_count_a++;
            uv_count_b++;
    
            }while(uv_count_b < 10);
       
            LINK_AT_STARTUP_A_TMP[uv_count_a + 1] = '\0';

            //traceit("I am here\n");
            //traceit("LINK_AT_STARTUP_A is --> %s\n", LINK_AT_STARTUP_A);
            //traceit("LINK_AT_STARTUP_A_TMP is --> %s\n", LINK_AT_STARTUP_A_TMP);            


            uv_count_a=0;
            uv_count_b=0;

            do
            {
              if (LINK_AT_STARTUP_B[uv_count_b] != ' ')
                LINK_AT_STARTUP_B_TMP[uv_count_a] = LINK_AT_STARTUP_B[uv_count_b];
              else
                uv_count_a--;

               uv_count_a++;
            uv_count_b++;
    
            }while(uv_count_b < 10);
       
            LINK_AT_STARTUP_B_TMP[uv_count_a + 1] = '\0';


            uv_count_a=0;
            uv_count_b=0;

            do
            {
              if (LINK_AT_STARTUP_C[uv_count_b] != ' ')
                LINK_AT_STARTUP_C_TMP[uv_count_a] = LINK_AT_STARTUP_C[uv_count_b];
              else
                uv_count_a--;

            uv_count_a++;
            uv_count_b++;
    
            }while(uv_count_b < 10);

             LINK_AT_STARTUP_C_TMP[uv_count_a + 1] = '\0';
            

            /* end of v3.15 mods */

            
            if (i == 0)
            {
              memset(temp_buff_a, '\0', sizeof temp_buff_a);
              memcpy(temp_buff_a, temp_buff, strlen(temp_buff)+1);
              //traceit("temp_buff_a is %s\n", temp_buff_a);
            }
            else
             if (i == 1)
             {
              memset(temp_buff_b, '\0', sizeof temp_buff_b);
              memcpy(temp_buff_b, temp_buff, strlen(temp_buff)+1);
             }
            else
             {
              memset(temp_buff_c, '\0', sizeof temp_buff_c);
              memcpy(temp_buff_c, temp_buff, strlen(temp_buff)+1);
             }

            /*** check for RF inactivity ***/
            if (to_remote_g2[i].is_connected)
            {
             if (strcmp( temp_buff_a, LINK_AT_STARTUP_A_TMP) != 0 || strcmp( temp_buff_b, LINK_AT_STARTUP_B_TMP) != 0 || strcmp( temp_buff_c, LINK_AT_STARTUP_C_TMP) != 0)
             // only go into this loop IF one of our modules is not linked to the default LINK_AT_STARTUP refelctor, etc...
             // since we do not want to allow our modules to timeout IF they are connected to the default host
             {
             
             if ((strcmp (temp_buff_a, LINK_AT_STARTUP_A_TMP) != 0 && i_tmp == 0))  // 0 means that our module A is connected to the default      
                  i=0;
         
             if ((strcmp (temp_buff_b, LINK_AT_STARTUP_B_TMP) != 0 && i_tmp == 1))
                  i=1;

             if ((strcmp (temp_buff_c, LINK_AT_STARTUP_C_TMP) != 0 && i_tmp == 2))     
                  i=2;


             // v3.16

             if (((strcmp (temp_buff_a, LINK_AT_STARTUP_A_TMP) != 0 && i == 0)) || ((strcmp (temp_buff_b, LINK_AT_STARTUP_B_TMP) != 0 && i == 1))
                  || ((strcmp (temp_buff_c, LINK_AT_STARTUP_C_TMP) != 0 && i == 2)))  
               if (((tnow - tracing[i].last_time) > RF_INACTIVITY_TIMER[i]) && (RF_INACTIVITY_TIMER[i] > 0))
               {
                  tracing[i].last_time = 0;


            // if(to_remote_g2[i].is_connected && strcmp(temp_buff,LINK_AT_STARTUP) != 0)
            //{

               // if (((tnow - tracing[i].last_time) > RF_INACTIVITY_TIMER[i]) && (RF_INACTIVITY_TIMER[i] > 0))
               //{
               //   tracing[i].last_time = 0;

                  // VA3UV v3.14

                  if ((to_remote_g2[i].from_mod == 'A') || (to_remote_g2[i].from_mod == 'B') || (to_remote_g2[i].from_mod == 'C'))

                     traceit("Unlinked from [%s] mod %c, local RF inactivity...\n", to_remote_g2[i].to_call, to_remote_g2[i].to_mod);

                  if (to_remote_g2[i].toDst4.sin_port == htons(RMT_REF_PORT))
                  {
                     queryCommand[0] = 5;
                     queryCommand[1] = 0;
                     queryCommand[2] = 24;
                     queryCommand[3] = 0;
                     queryCommand[4] = 0;
                     sendto(ref_g2_sock,(char *)queryCommand,5,0,
                            (struct sockaddr *)&(to_remote_g2[i].toDst4),
                            sizeof(to_remote_g2[i].toDst4));

                     /* zero out any other entries here that match that system */
                     for (j = 0; j < 3; j++)
                     {
                        if (j != i)
                        {
                           if ((to_remote_g2[j].toDst4.sin_addr.s_addr == to_remote_g2[i].toDst4.sin_addr.s_addr) &&
                               (to_remote_g2[j].toDst4.sin_port == htons(RMT_REF_PORT)))
                           {
                              to_remote_g2[j].to_call[0] = '\0';
                              memset(&(to_remote_g2[j].toDst4),0,sizeof(struct sockaddr_in));
                              to_remote_g2[j].from_mod = ' ';
                              to_remote_g2[j].to_mod = ' ';
                              to_remote_g2[j].countdown = 0;
                              to_remote_g2[j].is_connected = false;
                              to_remote_g2[j].in_streamid[0] = 0x00;
                              to_remote_g2[j].in_streamid[1] = 0x00;
                           }
                        }
                     }
                  }
                  else
                  if (to_remote_g2[i].toDst4.sin_port == htons(RMT_XRF_PORT))
                  //if (to_remote_g2[i].toDst4.sin_port == htons(RMT_XRF_PORT && (strcmp(to_remote_g2[i].link_status,LINK_AT_STARTUP) != 0 )))
                  {
                     strcpy(unlink_request, OWNER);
                     unlink_request[8] = to_remote_g2[i].from_mod;
                     unlink_request[9] = ' ';
                     unlink_request[10] = '\0';

                     for (j = 0; j < 5; j++)
                        sendto(xrf_g2_sock,unlink_request, CALL_SIZE + 3,0,
                               (struct sockaddr *)&(to_remote_g2[i].toDst4),
                               sizeof(to_remote_g2[i].toDst4));
                  }
                  else
                  if (to_remote_g2[i].toDst4.sin_port == htons(RMT_DCS_PORT))
                  {
                     strcpy(cmd_2_dcs, OWNER);
                     cmd_2_dcs[8] = to_remote_g2[i].from_mod;
                     cmd_2_dcs[9] = ' ';
                     cmd_2_dcs[10] = '\0';
                     memcpy(cmd_2_dcs + 11, to_remote_g2[i].to_call, 8);

                     for (j = 0; j < 2; j++)
                        sendto(dcs_g2_sock, cmd_2_dcs, 19 ,0,
                               (struct sockaddr *)&(to_remote_g2[i].toDst4),
                               sizeof(to_remote_g2[i].toDst4));
                  }


                  // VA3UV v3.14

                  if ((to_remote_g2[i].from_mod == 'A') || (to_remote_g2[i].from_mod == 'B') || (to_remote_g2[i].from_mod == 'C'))
                  {
                  
                    sprintf(notify_msg, "%c_unlinked.dat_UNLINKED_TIMEOUT", to_remote_g2[i].from_mod);
                    audio_notify(notify_msg);

                    to_remote_g2[i].to_call[0] = '\0';
                    memset(&(to_remote_g2[i].toDst4),0,sizeof(struct sockaddr_in));
                    to_remote_g2[i].from_mod = ' ';
                    to_remote_g2[i].to_mod = ' ';
                    to_remote_g2[i].countdown = 0;
                    to_remote_g2[i].is_connected = false;
                    to_remote_g2[i].in_streamid[0] = 0x00;
                    to_remote_g2[i].in_streamid[1] = 0x00;

                  print_status_file();

                  }
               }
               i=i_tmp;
            }
            }
         }         
         time(&hb);
      }

      FD_ZERO(&fdset);
      FD_SET(xrf_g2_sock,&fdset);
      FD_SET(dcs_g2_sock,&fdset);
      FD_SET(ref_g2_sock,&fdset);
      FD_SET(rptr_sock,&fdset);
      FD_SET(cmd_sock,&fdset);
      tv.tv_sec = 0;
      tv.tv_usec = 20000;
      (void)select(max_nfds + 1,&fdset,0,0,&tv);

      if (FD_ISSET(cmd_sock, &fdset))
      {
         fromlen = sizeof(struct sockaddr_in);
         recvlen2 = recvfrom(cmd_sock,(char *)readBuffer2,100,
                            0,(struct sockaddr *)&fromCmd,&fromlen);
         if (recvlen2 > 0)
         {
            readBuffer2[recvlen2 - 1] = '\0';
            handle_cmd((char *)readBuffer2);
         }
         FD_CLR (cmd_sock,&fdset);
      }

      if (FD_ISSET(xrf_g2_sock, &fdset))
      {
         fromlen = sizeof(struct sockaddr_in);
         recvlen2 = recvfrom(xrf_g2_sock,(char *)readBuffer2,100,
                            0,(struct sockaddr *)&fromDst4,&fromlen);

         strncpy(ip, inet_ntoa(fromDst4.sin_addr),IP_SIZE);
         ip[IP_SIZE] = '\0';
         strncpy(call, (char *)readBuffer2,CALL_SIZE);
         call[CALL_SIZE] = '\0';

         /* a packet of length (CALL_SIZE + 1) is a keepalive from repeater/reflector */
         if (recvlen2 == (CALL_SIZE + 1))
         {
            found = false;
            /* Find out if it is a keepalive from a repeater */
            for (i = 0; i < 3; i++)
            {
               if ((fromDst4.sin_addr.s_addr == to_remote_g2[i].toDst4.sin_addr.s_addr) &&
                   (to_remote_g2[i].type == 'x'))
               {
                  found = true;
                  if (!to_remote_g2[i].is_connected)
                  {
                     tracing[i].last_time = time(NULL);
                     to_remote_g2[i].is_connected = true;
                     traceit("Connected from: %.*s\n", recvlen2 - 1, readBuffer2);
                     print_status_file();

                     strcpy(linked_remote_system, to_remote_g2[i].to_call);
                     space_p = strchr(linked_remote_system, ' ');
                     if (space_p)
                        *space_p = '\0';
                     sprintf(notify_msg, "%c_linked.dat_LINKED_%s_%c", 
                            to_remote_g2[i].from_mod, 
                            linked_remote_system, 
                            to_remote_g2[i].to_mod);
                     audio_notify(notify_msg);

                  }
                  to_remote_g2[i].countdown = TIMEOUT;
               }
            }
         }
         else
         /* A packet of length (CALL_SIZE + 6) is either an ACK or a NAK from repeater-reflector */
         /* Because we sent a request before asking to link */
         if (recvlen2 == (CALL_SIZE + 6))
         {
            for (i = 0; i < 3; i++)
            {
               if ((fromDst4.sin_addr.s_addr == to_remote_g2[i].toDst4.sin_addr.s_addr) &&
                   (to_remote_g2[i].type == 'x'))
               {
                  if ((memcmp((char *)readBuffer2 + 10, "ACK", 3) == 0) &&
                      (to_remote_g2[i].from_mod == readBuffer2[8]))
                  {
                     if (!to_remote_g2[i].is_connected)
                     {
                        tracing[i].last_time = time(NULL);
                        to_remote_g2[i].is_connected = true;
                        traceit("Connected from: [%s] %c\n",
                              to_remote_g2[i].to_call, to_remote_g2[i].to_mod);
                        print_status_file();

                        strcpy(linked_remote_system, to_remote_g2[i].to_call);
                        space_p = strchr(linked_remote_system, ' ');
                        if (space_p)
                           *space_p = '\0';
                        sprintf(notify_msg, "%c_linked.dat_LINKED_%s_%c",
                            to_remote_g2[i].from_mod,
                            linked_remote_system,
                            to_remote_g2[i].to_mod);
                        audio_notify(notify_msg);
                     }
                  }
                  else
                  if ((memcmp((char *)readBuffer2 + 10, "NAK", 3) == 0) &&
                      (to_remote_g2[i].from_mod == readBuffer2[8]))
                  {
                     traceit("Link module %c to [%s] %c is rejected\n",
                              to_remote_g2[i].from_mod, to_remote_g2[i].to_call, 
                              to_remote_g2[i].to_mod);

                     sprintf(notify_msg, "%c_failed_linked.dat_FAILED_TO_LINK",
                             to_remote_g2[i].from_mod);
                     audio_notify(notify_msg);

                     to_remote_g2[i].type = ' ';
                     to_remote_g2[i].to_call[0] = '\0';
                     memset(&(to_remote_g2[i].toDst4),0,sizeof(struct sockaddr_in));
                     to_remote_g2[i].from_mod = ' ';
                     to_remote_g2[i].to_mod = ' ';
                     to_remote_g2[i].countdown = 0;
                     to_remote_g2[i].is_connected = false;
                     to_remote_g2[i].in_streamid[0] = 0x00;
                     to_remote_g2[i].in_streamid[1] = 0x00;

                     print_status_file();
                  }
               }
            }
         }
         else
         /* 
            A packet of length (CALL_SIZE + 3) is a request 
            from a remote repeater to link-unlink with our repeater 
         */
         if (recvlen2 == CALL_SIZE + 3)
         {
            /* Check our linked repeaters/reflectors */
            for (i = 0; i < 3; i++)
            {
               if ((fromDst4.sin_addr.s_addr == to_remote_g2[i].toDst4.sin_addr.s_addr) &&
                   (to_remote_g2[i].type == 'x'))
               {
                  if (to_remote_g2[i].to_mod == readBuffer2[8])
                  {
                     /* unlink request from remote repeater that we know */
                     if (readBuffer2[9] == ' ')
                     {
                        traceit("Received: %.*s\n", recvlen2 - 1, readBuffer2);
                        traceit("Module %c to [%s] %c is unlinked\n",
                              to_remote_g2[i].from_mod, 
                              to_remote_g2[i].to_call, to_remote_g2[i].to_mod);

                        sprintf(notify_msg, "%c_unlinked.dat_UNLINKED", to_remote_g2[i].from_mod);
                        audio_notify(notify_msg);

                        //v3.18

                        sprintf(df_b, "/dstar/tmp/blocklinking-%c", tolower(to_remote_g2[i].from_mod));
                        unlink(df_b);

                        to_remote_g2[i].type = ' ';
                        to_remote_g2[i].to_call[0] = '\0';
                        memset(&(to_remote_g2[i].toDst4),0,sizeof(struct sockaddr_in));
                        to_remote_g2[i].from_mod = ' ';
                        to_remote_g2[i].to_mod = ' ';
                        to_remote_g2[i].countdown = 0;
                        to_remote_g2[i].is_connected = false;
                        to_remote_g2[i].in_streamid[0] = 0x00;
                        to_remote_g2[i].in_streamid[1] = 0x00;

                        print_status_file();
                     }
                     else
                     /* link request from a remote repeater that we know */
                     if (
                           ((i == 0) && (readBuffer2[9] == 'A')) ||
                           ((i == 1) && (readBuffer2[9] == 'B')) ||
                           ((i == 2) && (readBuffer2[9] == 'C'))
                        )
                     {
                        /* 
                           I HAVE TO ADD CODE here to PREVENT the REMOTE NODE
                           from LINKING one of their remote modules to
                           more than one of our local modules
                        */
       
                        // v3.18
                        df_block(tolower(readBuffer2[9]));
                        //

                        traceit("Received: %.*s\n", recvlen2 - 1, readBuffer2);

                        to_remote_g2[i].type = 'x';
                        strncpy(to_remote_g2[i].to_call, (char *)readBuffer2,CALL_SIZE);
                        to_remote_g2[i].to_call[CALL_SIZE] = '\0';
                        memcpy(&(to_remote_g2[i].toDst4), &fromDst4, sizeof(struct sockaddr_in));
                        to_remote_g2[i].toDst4.sin_port = htons(RMT_XRF_PORT);
                        to_remote_g2[i].to_mod = readBuffer2[8];
                        to_remote_g2[i].countdown = TIMEOUT;
                        to_remote_g2[i].is_connected = true;
                        to_remote_g2[i].in_streamid[0] = 0x00;
                        to_remote_g2[i].in_streamid[1] = 0x00;

                        traceit("Module %c to [%s] %c linked\n",
                              readBuffer2[9],
                              to_remote_g2[i].to_call, to_remote_g2[i].to_mod);

                        tracing[i].last_time = time(NULL);

                        print_status_file();


                        /* send back an ACK */
                        memcpy(readBuffer2 + 10, "ACK", 4);
                        sendto(xrf_g2_sock, (char *)readBuffer2, CALL_SIZE + 6,
                                        0,(struct sockaddr *)&(to_remote_g2[i].toDst4),
                                        sizeof(struct sockaddr_in));

                        if (to_remote_g2[i].from_mod != readBuffer2[9])
                        {
                           to_remote_g2[i].from_mod = readBuffer2[9];

                           strcpy(linked_remote_system, to_remote_g2[i].to_call);
                           space_p = strchr(linked_remote_system, ' ');
                           if (space_p)
                              *space_p = '\0';
                           sprintf(notify_msg, "%c_linked.dat_LINKED_%s_%c",
                                   to_remote_g2[i].from_mod,
                                   linked_remote_system,
                                   to_remote_g2[i].to_mod);
                           audio_notify(notify_msg);
                        }
                     }
                  }
               }
            }

            /* link request from remote repeater that is not yet linked to our system */
            /* find out which of our local modules the remote repeater is interested in */
            i = -1;
            if (readBuffer2[9] == 'A')
               i = 0;
            else
            if (readBuffer2[9] == 'B')
               i = 1;
            else
            if (readBuffer2[9] == 'C')
               i = 2;

            /* Is this repeater listed in gwys.txt? */
            gwy_pos = gwy_list.find(call);
            if (gwy_pos == gwy_list.end())
            {
               /* We did NOT find this repeater in gwys.txt, reject the incoming link request */
               traceit("Incoming link from %s,%s but not found in gwys.txt\n",call,ip);
               i = -1;
            }
            else
            {
               rc = regexec(&preg, call, 0, NULL, 0);
               if (rc != 0)
               {
                  traceit("Invalid repeater %s,%s requesting to link\n", call, ip);
                  i = -1;
               }
            }
            if (i >= 0)
            {
               /* Is the local repeater module linked to anything ? */
               if (to_remote_g2[i].to_mod == ' ')
               {
                  if ((readBuffer2[8] == 'A') || (readBuffer2[8] == 'B') || (readBuffer2[8] == 'C') ||
                      (readBuffer2[8] == 'D') || (readBuffer2[8] == 'E'))
                  {
                     /*
                        I HAVE TO ADD CODE here to PREVENT the REMOTE NODE
                        from LINKING one of their remote modules to
                        more than one of our local modules
                     */

                     /* now it can be added as a repeater */
                     to_remote_g2[i].type = 'x';
                     strcpy(to_remote_g2[i].to_call, call);
                     to_remote_g2[i].to_call[CALL_SIZE] = '\0';
                     memcpy(&(to_remote_g2[i].toDst4), &fromDst4, sizeof(struct sockaddr_in));
                     to_remote_g2[i].toDst4.sin_port = htons(RMT_XRF_PORT);
                     to_remote_g2[i].from_mod = readBuffer2[9];
                     to_remote_g2[i].to_mod = readBuffer2[8];
                     to_remote_g2[i].countdown = TIMEOUT;
                     to_remote_g2[i].is_connected = true;
                     to_remote_g2[i].in_streamid[0] = 0x00;
                     to_remote_g2[i].in_streamid[1] = 0x00;

                     print_status_file();
                     tracing[i].last_time = time(NULL);

                     traceit("Received: %.*s\n", recvlen2 - 1, readBuffer2);
                     traceit("Module %c to [%s] %c linked\n",
                              to_remote_g2[i].from_mod,
                              to_remote_g2[i].to_call, to_remote_g2[i].to_mod);

                     strcpy(linked_remote_system, to_remote_g2[i].to_call);
                     space_p = strchr(linked_remote_system, ' ');
                     if (space_p)
                        *space_p = '\0';
                     sprintf(notify_msg, "%c_linked.dat_LINKED_%s_%c",
                            to_remote_g2[i].from_mod,
                            linked_remote_system,
                            to_remote_g2[i].to_mod);
                     audio_notify(notify_msg);

                     /* send back an ACK */
                     memcpy(readBuffer2 + 10, "ACK", 4);
                     sendto(xrf_g2_sock, (char *)readBuffer2, CALL_SIZE + 6,
                            0,(struct sockaddr *)&(to_remote_g2[i].toDst4),
                            sizeof(struct sockaddr_in));
                  }
               }
               else
               {
                  if (fromDst4.sin_addr.s_addr != to_remote_g2[i].toDst4.sin_addr.s_addr)
                  {
                     /* Our repeater module is linked to another repeater-reflector */
                     memcpy(readBuffer2 + 10, "NAK", 4);
                     fromDst4.sin_port = htons(RMT_XRF_PORT);
                     sendto(xrf_g2_sock, (char *)readBuffer2, CALL_SIZE + 6,
                         0,(struct sockaddr *)&fromDst4,
                         sizeof(struct sockaddr_in));
                  }
               }
            }         
         }
         else
         if ( ((recvlen2 == 56) || 
               (recvlen2 == 27)) &&
              (memcmp(readBuffer2, "DSVT", 4) == 0) &&
              ((readBuffer2[4] == 0x10) || 
               (readBuffer2[4] == 0x20)) && 
              (readBuffer2[8] == 0x20))
         {
            /* reset countdown and protect against hackers */

            found = false;
            for (i = 0; i < 3; i++)
            {
               if ((fromDst4.sin_addr.s_addr == to_remote_g2[i].toDst4.sin_addr.s_addr) &&
                   (to_remote_g2[i].type == 'x'))
               {
                  to_remote_g2[i].countdown = TIMEOUT;
                  found = true;
               }
            }

            /* process header */
            if ((recvlen2 == 56) && found) 
            {
               memset(source_stn, ' ', 9); source_stn[8] = '\0';

               /* some bad hotspot programs out there using INCORRECT flag */
               if (readBuffer2[15] == 0x40)
                  readBuffer2[15] = 0x00;
               else
               if (readBuffer2[15] == 0x48)
                  readBuffer2[15] = 0x08;
               else
               if (readBuffer2[15] == 0x60)
                  readBuffer2[15] = 0x20;
               else
               if (readBuffer2[15] == 0x68)
                  readBuffer2[15] = 0x28;

               /* A reflector will send to us its own RPT1 */
               /* A repeater will send to us our RPT1 */

               for (i = 0; i < 3; i++)
               {
                  /* v3.18 if ((fromDst4.sin_addr.s_addr == to_remote_g2[i].toDst4.sin_addr.s_addr) &&
                      (to_remote_g2[i].type == 'x'))
                  { */

                   if ((fromDst4.sin_addr.s_addr == to_remote_g2[i].toDst4.sin_addr.s_addr))

                   {

                     /* it is a reflector, reflector's rpt1 */
                    //if  ((memcmp(readBuffer2 + 18, to_remote_g2[i].to_call, 7) == 0) &&
                    //      (readBuffer2[25] == to_remote_g2[i].to_mod))
                    //{

                        memcpy(&readBuffer2[18], OWNER, CALL_SIZE);
                        readBuffer2[25] = to_remote_g2[i].from_mod;
                        memcpy(&readBuffer2[34], "CQCQCQ  ", 8);

                        memcpy(source_stn, to_remote_g2[i].to_call, 8); source_stn[7] = to_remote_g2[i].to_mod;

                        break;
                     //}
                     /* else
                     // it is a repeater, our rpt1
                     if ((memcmp(readBuffer2 + 18, OWNER, 7)) &&
                         (readBuffer2[25] == to_remote_g2[i].from_mod))
                     {
                        memcpy(source_stn, to_remote_g2[i].to_call, 8); source_stn[7] = to_remote_g2[i].to_mod;

                        break;
                     } */
                 }
               }

               /* somebody's crazy idea of having a personal callsign in RPT2 */
               /* we must set it to our gateway callsign */
               memcpy(&readBuffer2[26], OWNER, CALL_SIZE);
               readBuffer2[33] = 'G';
               readBuffer2[6] = 0x00;
               calcPFCS(readBuffer2,56);

               /* At this point, all data have our RPT1 and RPT2 */

               /* send the data to the repeater/reflector that is linked to our RPT1 */
               i = -1;
               if (readBuffer2[25] == 'A')
                  i = 0;
               else
               if (readBuffer2[25] == 'B')
                  i = 1;
               else
               if (readBuffer2[25] == 'C')
                  i = 2;

               /* are we sure that RPT1 is our system? */
               if ((memcmp(readBuffer2 + 18, OWNER, 7) == 0) && (i >= 0))
               {
                  /* Last Heard */
                  if (memcmp(old_sid[i].sid, readBuffer2 + 12, 2) != 0)
                  {
                     if (QSO_DETAILS)
                        traceit("START from remote g2: streamID=%d,%d, flags=%02x:%02x:%02x, my=%.8s, sfx=%.4s, ur=%.8s, rpt1=%.8s, rpt2=%.8s, %d bytes fromIP=%s, source=%.8s\n",
                                readBuffer2[12],readBuffer2[13],
                                readBuffer2[15], readBuffer2[16], readBuffer2[17],
                                &readBuffer2[42],
                                &readBuffer2[50], &readBuffer2[34],
                                &readBuffer2[18], &readBuffer2[26],
                                recvlen2,inet_ntoa(fromDst4.sin_addr), source_stn);

 
                     // put user into tmp1
                     memcpy(tmp1, readBuffer2 + 42, 8); tmp1[8] = '\0';
                     


                     // delete the user if exists
                     for (dt_lh_pos = dt_lh_list.begin(); dt_lh_pos != dt_lh_list.end();  dt_lh_pos++)
                     {
                        if (strcmp((char *)dt_lh_pos->second.c_str(), tmp1) == 0)
                        {
                           dt_lh_list.erase(dt_lh_pos);
                           break;
                        }
                     }
                     /* Limit?, delete oldest user */
                     if (dt_lh_list.size() == LH_MAX_SIZE)
                     {
                        dt_lh_pos = dt_lh_list.begin();
                        dt_lh_list.erase(dt_lh_pos);
                     }
                     // add user
                     time(&tnow);
                     sprintf(tmp2, "%ld=r%.6s%c%c", tnow, source_stn, source_stn[7], readBuffer2[25]);
                     dt_lh_list[tmp2] = tmp1;

                     memcpy(old_sid[i].sid, readBuffer2 + 12, 2);
                  }

                  /* relay data to our local G2 */
                  sendto(xrf_g2_sock, (char *)readBuffer2,56,0,(struct sockaddr *)&toLocalg2,sizeof(struct sockaddr_in));

                  /* send data to donglers */
                  /* no changes here */
                  for (pos = inbound_list.begin(); pos != inbound_list.end(); pos++)
                  {
                     inbound_ptr = (inbound *)pos->second;
                     if (fromDst4.sin_addr.s_addr != inbound_ptr->sin.sin_addr.s_addr)
                     {
                        readBuffer[0] = (unsigned char)(58 & 0xFF);
                        readBuffer[1] = (unsigned char)(58 >> 8 & 0x1F);
                        readBuffer[1] = (unsigned char)(readBuffer[1] | 0xFFFFFF80);
                        memcpy(readBuffer + 2, readBuffer2, 56);

                        sendto(ref_g2_sock, (char *)readBuffer, 58, 0,
                               (struct sockaddr *)&(inbound_ptr->sin),
                               sizeof(struct sockaddr_in));
                     }
                     else
                        inbound_ptr->mod = readBuffer2[25];
                  } 

                  /* Is there another local module linked to the remote same xrf mod ? */
                  /* If Yes, then broadcast */
                  k = i + 1;

                  if (k < 3)
                  {
                     brd_from_xrf_idx = 0;
                     streamid_raw = (readBuffer2[12] * 256U) + readBuffer2[13];

                     /* We can only enter this loop up to 2 times max */
                     for (j = k; j < 3; j++)
                     {
                        /* it is a remote gateway, not a dongle user */
                        if ((fromDst4.sin_addr.s_addr == to_remote_g2[j].toDst4.sin_addr.s_addr) &&
                            /* it is xrf */
                            (to_remote_g2[j].type == 'x') &&
                            (memcmp(to_remote_g2[j].to_call, "XRF", 3) == 0) &&
                            /* it is the same xrf and xrf module */
                            (memcmp(to_remote_g2[j].to_call, to_remote_g2[i].to_call, 8) == 0) &&
                            (to_remote_g2[j].to_mod == to_remote_g2[i].to_mod))
                        {
                           /* send the packet to another module of our local repeater: this is multi-link */

                           /* generate new packet */
                           memcpy(from_xrf_torptr_brd, readBuffer2, 56);

                           /* different repeater module */
                           from_xrf_torptr_brd[25] = to_remote_g2[j].from_mod;

                           /* assign new streamid */
                           streamid_raw ++;
                           if (streamid_raw == 0)
                              streamid_raw ++;
                           from_xrf_torptr_brd[12] = streamid_raw / 256U;
                           from_xrf_torptr_brd[13] = streamid_raw % 256U;

                           calcPFCS(from_xrf_torptr_brd, 56);

                           /* send the data to the local gateway/repeater */
                           sendto(xrf_g2_sock, (char *)from_xrf_torptr_brd,56,0,
                                  (struct sockaddr *)&toLocalg2,sizeof(struct sockaddr_in));

                           /* save streamid for use with the audio packets that will arrive after this header */

                           brd_from_xrf.xrf_streamid[0] = readBuffer2[12];
                           brd_from_xrf.xrf_streamid[1] = readBuffer2[13];
                           brd_from_xrf.rptr_streamid[brd_from_xrf_idx][0] = from_xrf_torptr_brd[12];
                           brd_from_xrf.rptr_streamid[brd_from_xrf_idx][1] = from_xrf_torptr_brd[13];
                           brd_from_xrf_idx ++;
                        }
                     }
                  }

                  if ((to_remote_g2[i].toDst4.sin_addr.s_addr != fromDst4.sin_addr.s_addr) &&
                      to_remote_g2[i].is_connected)
                  {
                     if (to_remote_g2[i].type == 'x')
                     {
                        if ((memcmp(readBuffer2 + 42, OWNER, 7) != 0) &&         /* block repeater announcements */
                            (memcmp(readBuffer2 + 34, "CQCQCQ", 6) == 0) &&     /* CQ calls only */
                            ((readBuffer2[15] == 0x00)  ||                       /* normal */
                             (readBuffer2[15] == 0x08)  ||                       /* EMR */
                             (readBuffer2[15] == 0x20)  ||                       /* BK */
                             (readBuffer2[15] == 0x28)) &&                       /* EMR + BK */
                            (memcmp(readBuffer2 + 26, OWNER, 7) == 0) &&         /* rpt2 must be us */
                            (readBuffer2[33] == 'G'))
                        {
                           to_remote_g2[i].in_streamid[0] = readBuffer2[12];
                           to_remote_g2[i].in_streamid[1] = readBuffer2[13];

                           /* inform XRF about the source */
                           readBuffer2[11] = to_remote_g2[i].from_mod;

                           memcpy((char *)readBuffer2 + 18, to_remote_g2[i].to_call, CALL_SIZE);
                           readBuffer2[25] = to_remote_g2[i].to_mod;
                           memcpy((char *)readBuffer2 + 26, to_remote_g2[i].to_call, CALL_SIZE);
                           readBuffer2[33] = 'G';
                           calcPFCS(readBuffer2, 56);

                           sendto(xrf_g2_sock, (char *)readBuffer2, 56, 0,
                                  (struct sockaddr *)&(to_remote_g2[i].toDst4),
                                  sizeof(struct sockaddr_in));
                        }
                     }
                     else
                     if (to_remote_g2[i].type == 'p')
                     {
                        /* we must NOT send an INVALID mycall to remote REF */
                        memcpy(call, readBuffer2 + 42, CALL_SIZE);
                        call[CALL_SIZE] = '\0';
                        if (valid_callsigns.find(call) == valid_callsigns.end())
                           traceit("Invalid mycall=[%s] will not be transmitted\n", call);
                        else
                        {
                           if ((memcmp(readBuffer2 + 42, OWNER, 7) != 0) &&         /* block repeater announcements */
                               (memcmp(readBuffer2 + 34, "CQCQCQ", 6) == 0) &&     /* CQ calls only */
                               ((readBuffer2[15] == 0x00)  ||                       /* normal */
                                (readBuffer2[15] == 0x08)  ||                       /* EMR */
                                (readBuffer2[15] == 0x20)  ||                       /* BK */
                                (readBuffer2[15] == 0x28)) &&                       /* EMR + BK */
                               (memcmp(readBuffer2 + 26, OWNER, 7) == 0) &&         /* rpt2 must be us */
                               (readBuffer2[33] == 'G'))
                           {
                              to_remote_g2[i].in_streamid[0] = readBuffer2[12];
                              to_remote_g2[i].in_streamid[1] = readBuffer2[13];

                              readBuffer[0] = (unsigned char)(58 & 0xFF);
                              readBuffer[1] = (unsigned char)(58 >> 8 & 0x1F);
                              readBuffer[1] = (unsigned char)(readBuffer[1] | 0xFFFFFF80);

                              memcpy(readBuffer + 2, readBuffer2, 56);

                              /*** SHIT SHIT start ***/
                              readBuffer[11] = 0x00;
                              readBuffer[12] = 0x01;
                              readBuffer[13] = 0x02;
                              memcpy(readBuffer + 20, OWNER, CALL_SIZE);
                              readBuffer[27] = to_remote_g2[i].from_mod;
                              memcpy(readBuffer + 28, OWNER, CALL_SIZE);
                              readBuffer[35] = 'G';
                              calcPFCS(readBuffer + 2, 56);
                              /*** SHIT SHIT end ***/

                              sendto(ref_g2_sock, (char *)readBuffer, 58, 0,
                                     (struct sockaddr *)&(to_remote_g2[i].toDst4),
                                     sizeof(struct sockaddr_in));
                           }
                        }
                     }
                     else
                     if (to_remote_g2[i].type == 'd')
                     {
                        if ((memcmp(readBuffer2 + 42, OWNER, 7) != 0) &&         /* block repeater announcements */
                            (memcmp(readBuffer2 + 34, "CQCQCQ", 6) == 0) &&     /* CQ calls only */
                            ((readBuffer2[15] == 0x00)  ||                       /* normal */
                             (readBuffer2[15] == 0x08)  ||                       /* EMR */
                             (readBuffer2[15] == 0x20)  ||                       /* BK */
                             (readBuffer2[15] == 0x28)) &&                       /* EMR + BK */
                            (memcmp(readBuffer2 + 26, OWNER, 7) == 0) &&         /* rpt2 must be us */
                            (readBuffer2[33] == 'G'))
                        {
                           to_remote_g2[i].in_streamid[0] = readBuffer2[12];
                           to_remote_g2[i].in_streamid[1] = readBuffer2[13];

                           memcpy(xrf_2_dcs[i].mycall, readBuffer2 + 42, 8);
                           memcpy(xrf_2_dcs[i].sfx, readBuffer2 + 50, 4);
                           xrf_2_dcs[i].dcs_rptr_seq = 0;
                        }
                     }
                  }
               }
            }
            else
            if (found)
            {
               readBuffer2[6] = 0x00;

               if ((readBuffer2[14] & 0x40) != 0)
               {
                  for (i = 0; i < 3; i++)
                  {
                     if (memcmp(old_sid[i].sid, readBuffer2 + 12, 2) == 0)
                     {
                        if (QSO_DETAILS)
                           traceit("END from remote g2: streamID=%d,%d, %d bytes from IP=%s\n",
                                   readBuffer2[12],readBuffer2[13],recvlen2,inet_ntoa(fromDst4.sin_addr));

                        memset(old_sid[i].sid, 0x00, 2);
                        break;
                     }
                  }
               }

               /* relay data to our local G2 */
               sendto(xrf_g2_sock, (char *)readBuffer2,27,0,(struct sockaddr *)&toLocalg2,sizeof(struct sockaddr_in));

               /* send data to donglers */
               /* no changes here */
               for (pos = inbound_list.begin(); pos != inbound_list.end(); pos++)
               {
                  inbound_ptr = (inbound *)pos->second;
                  if (fromDst4.sin_addr.s_addr != inbound_ptr->sin.sin_addr.s_addr)
                  {
                     readBuffer[0] = (unsigned char)(29 & 0xFF);
                     readBuffer[1] = (unsigned char)(29 >> 8 & 0x1F);
                     readBuffer[1] = (unsigned char)(readBuffer[1] | 0xFFFFFF80);

                     memcpy(readBuffer + 2, readBuffer2, 27);

                     sendto(ref_g2_sock, (char *)readBuffer, 29,
                            0,(struct sockaddr *)&(inbound_ptr->sin),
                            sizeof(struct sockaddr_in));
                  }
               }

               /* do we have to broadcast ? */
               if (memcmp(brd_from_xrf.xrf_streamid, readBuffer2 + 12, 2) == 0)
               {
                  memcpy(from_xrf_torptr_brd, readBuffer2, 27);

                  if ((brd_from_xrf.rptr_streamid[0][0] != 0x00) ||
                      (brd_from_xrf.rptr_streamid[0][1] != 0x00))
                  {
                     from_xrf_torptr_brd[12] = brd_from_xrf.rptr_streamid[0][0];
                     from_xrf_torptr_brd[13] = brd_from_xrf.rptr_streamid[0][1];
                     sendto(xrf_g2_sock, (char *)from_xrf_torptr_brd,27,0,(struct sockaddr *)&toLocalg2,sizeof(struct sockaddr_in));
                  }

                  if ((brd_from_xrf.rptr_streamid[1][0] != 0x00) ||
                      (brd_from_xrf.rptr_streamid[1][1] != 0x00))
                  {
                     from_xrf_torptr_brd[12] = brd_from_xrf.rptr_streamid[1][0];
                     from_xrf_torptr_brd[13] = brd_from_xrf.rptr_streamid[1][1];
                     sendto(xrf_g2_sock, (char *)from_xrf_torptr_brd,27,0,(struct sockaddr *)&toLocalg2,sizeof(struct sockaddr_in));
                  }

                  if ((readBuffer2[14] & 0x40) != 0)
                  {
                     brd_from_xrf.xrf_streamid[0] = brd_from_xrf.xrf_streamid[1] = 0x00;
                     brd_from_xrf.rptr_streamid[0][0] = brd_from_xrf.rptr_streamid[0][1] = 0x00;
                     brd_from_xrf.rptr_streamid[1][0] = brd_from_xrf.rptr_streamid[1][1] = 0x00;
                     brd_from_xrf_idx = 0;
                  }
               }

               for (i = 0; i < 3; i++)
               {
                  if ((to_remote_g2[i].is_connected) &&
                      (to_remote_g2[i].toDst4.sin_addr.s_addr != fromDst4.sin_addr.s_addr) &&
                      (memcmp(to_remote_g2[i].in_streamid, readBuffer2 + 12, 2) == 0))
                  {
                     if (to_remote_g2[i].type == 'x')
                     {
                        /* inform XRF about the source */
                        readBuffer2[11] = to_remote_g2[i].from_mod;

                        sendto(xrf_g2_sock, (char *)readBuffer2, 27, 0,
                               (struct sockaddr *)&(to_remote_g2[i].toDst4),
                               sizeof(struct sockaddr_in));
                     }
                     else
                     if (to_remote_g2[i].type == 'p')
                     {
                        readBuffer[0] = (unsigned char)(29 & 0xFF);
                        readBuffer[1] = (unsigned char)(29 >> 8 & 0x1F);
                        readBuffer[1] = (unsigned char)(readBuffer[1] | 0xFFFFFF80);

                        memcpy(readBuffer + 2, readBuffer2, 27);

                        /*** SHIT SHIT start ***/
                        readBuffer[11] = 0x00;
                        readBuffer[12] = 0x01;
                        readBuffer[13] = 0x02;
                        /*** SHIT SHIT end ***/

                        sendto(ref_g2_sock, (char *)readBuffer, 29,
                               0,(struct sockaddr *)&(to_remote_g2[i].toDst4),
                               sizeof(struct sockaddr_in));
                     }
                     else
                     if (to_remote_g2[i].type == 'd')
                     {
                        memset(dcs_buf, 0x00, 600);
                        dcs_buf[0] = dcs_buf[1] = dcs_buf[2] = '0';
                        dcs_buf[3] = '1';
                        dcs_buf[4] = dcs_buf[5] = dcs_buf[6] = 0x00;
                        memcpy(dcs_buf + 7, to_remote_g2[i].to_call, 8);
                        dcs_buf[14] = to_remote_g2[i].to_mod;
                        memcpy(dcs_buf + 15, OWNER, 8);
                        dcs_buf[22] = to_remote_g2[i].from_mod;
                        memcpy(dcs_buf + 23, "CQCQCQ  ", 8);
                        memcpy(dcs_buf + 31, xrf_2_dcs[i].mycall, 8);
                        memcpy(dcs_buf + 39, xrf_2_dcs[i].sfx, 4);
                        dcs_buf[43] = readBuffer2[12];  /* streamid0 */
                        dcs_buf[44] = readBuffer2[13];  /* streamid1 */
                        dcs_buf[45] = readBuffer2[14];  /* cycle sequence */
                        memcpy(dcs_buf + 46, readBuffer2 + 15, 12);

                        dcs_buf[58] = (xrf_2_dcs[i].dcs_rptr_seq >> 0)  & 0xff;
                        dcs_buf[59] = (xrf_2_dcs[i].dcs_rptr_seq >> 8)  & 0xff;
                        dcs_buf[60] = (xrf_2_dcs[i].dcs_rptr_seq >> 16) & 0xff;

                        xrf_2_dcs[i].dcs_rptr_seq ++;

                        dcs_buf[61] = 0x01;
                        dcs_buf[62] = 0x00;

                        sendto(dcs_g2_sock, dcs_buf, 100, 0,
                                  (struct sockaddr *)&(to_remote_g2[i].toDst4),
                                  sizeof(to_remote_g2[i].toDst4));
                     }

                     if ((readBuffer2[14] & 0x40) != 0)
                     {
                        to_remote_g2[i].in_streamid[0] = 0x00;
                        to_remote_g2[i].in_streamid[1] = 0x00;
                     }
                     break;
                  }
               }
            }
         }
         FD_CLR (xrf_g2_sock,&fdset);
      }

      if (FD_ISSET(ref_g2_sock, &fdset))
      {
         fromlen = sizeof(struct sockaddr_in);
         recvlen2 = recvfrom(ref_g2_sock,(char *)readBuffer2,100,
                            0,(struct sockaddr *)&fromDst4,&fromlen);

         if (recvlen2 == 9)
         {
            /* v3.18 if (fromDst4.sin_addr.s_addr == to_auth0.sin_addr.s_addr)
            {
               if (memcmp(readBuffer2, rep_from_auth0_ok, 5) == 0)
               {
                  if (memcmp(readBuffer2 + 5, rep_from_auth0_ok + 5, 4) != 0)
                  {
                     if (QSO_DETAILS)
                        traceit("auth0: new seed=%02x %02x %02x %02x, old seed=%02x %02x %02x %02x\n", 
                                readBuffer2[5], readBuffer2[6], readBuffer2[7], readBuffer2[8],
                                rep_from_auth0_ok[5], rep_from_auth0_ok[6], 
                                rep_from_auth0_ok[7], rep_from_auth0_ok[8]);
                  }
                  memcpy(rep_from_auth0_ok, readBuffer2, 9);
                  if (!auth0_linking_ok && (memcmp(rep_from_auth0_ok + 5, "\000\000\000\000", 4) != 0))
                  {
                     auth0_linking_ok = true;
                     traceit("Linking enabled from auth0\n");
                  }
                  sendto(ref_g2_sock, rep_to_auth_ok, 9, 0,
                         (struct sockaddr *)&fromDst4, sizeof(struct sockaddr_in));
               }
            } */
            /* if (fromDst4.sin_addr.s_addr == to_auth1.sin_addr.s_addr)
            {
               if (memcmp(readBuffer2, rep_from_auth1_ok, 5) == 0)
               {
                  if (memcmp(readBuffer2 + 5, rep_from_auth1_ok + 5, 4) != 0)
                  {
                     if (QSO_DETAILS)
                        traceit("auth1: new seed=%02x %02x %02x %02x, old seed=%02x %02x %02x %02x\n",
                                readBuffer2[5], readBuffer2[6], readBuffer2[7], readBuffer2[8],
                                rep_from_auth1_ok[5], rep_from_auth1_ok[6],
                                rep_from_auth1_ok[7], rep_from_auth1_ok[8]);
                  }
                  memcpy(rep_from_auth1_ok, readBuffer2, 9);
                  if (!auth1_linking_ok && (memcmp(rep_from_auth1_ok + 5, "\000\000\000\000", 4) != 0))
                  {
                     auth1_linking_ok = true;
                     traceit("Linking enabled from auth1\n");
                  }
                  sendto(ref_g2_sock, rep_to_auth_ok, 9, 0,
                         (struct sockaddr *)&fromDst4, sizeof(struct sockaddr_in));
               }
            } */
         }

         strncpy(ip, inet_ntoa(fromDst4.sin_addr),IP_SIZE);
         ip[IP_SIZE] = '\0';

         found = false;

         /* LH */
         if ((recvlen2 == 4) &&
             (readBuffer2[0] == 4) &&
             (readBuffer2[1] == 192) &&
             (readBuffer2[2] == 7) &&
             (readBuffer2[3] == 0))
         {
            unsigned short j_idx = 0;
            unsigned short k_idx = 0;
            unsigned char tmp[2];

            pos = inbound_list.find(ip);
            if (pos != inbound_list.end())
            {
               inbound_ptr = (inbound *)pos->second;
               /* traceit("Remote station %s %s requested LH list\n", inbound_ptr->call, ip); */

               /* header is 10 bytes */

               /* reply type */
               readBuffer2[2] = 7;
               readBuffer2[3] = 0;

               /* it looks like time_t here */
               time(&tnow);
               memcpy((char *)readBuffer2 + 6, (char *)&tnow, sizeof(time_t));

               for (r_dt_lh_pos = dt_lh_list.rbegin(); r_dt_lh_pos != dt_lh_list.rend();  r_dt_lh_pos++)
               {
                  /* each entry has 24 bytes */

                  /* start at position 10 to bypass the header */
                  strcpy((char *)readBuffer2 + 10 + (24 * j_idx), r_dt_lh_pos->second.c_str());   
                  p = strchr((char *)r_dt_lh_pos->first.c_str(), '=');
                  if (p)
                  {
                     memcpy((char *)readBuffer2 + 18 + (24 * j_idx), p + 2, 8);

                     /* if local or local w/gps */
                     if ((p[1] == 'l') || (p[1] == 'g'))
                        readBuffer2[18 + (24 * j_idx) + 6] = *(p + 1); 

                     *p = '\0';
                     tnow = atol(r_dt_lh_pos->first.c_str());
                     *p = '=';
                     memcpy((char *)readBuffer2 + 26 + (24 * j_idx), &tnow, sizeof(time_t));
                  } 
                  else
                  {
                     memcpy((char *)readBuffer2 + 18 + (24 * j_idx), "ERROR   ", 8);
                     time(&tnow);
                     memcpy((char *)readBuffer2 + 26 + (24 * j_idx), &tnow, sizeof(time_t));
                  }

                  readBuffer2[30 + (24 * j_idx)] = 0;
                  readBuffer2[31 + (24 * j_idx)] = 0;
                  readBuffer2[32 + (24 * j_idx)] = 0;
                  readBuffer2[33 + (24 * j_idx)] = 0;

                  j_idx++;

                  /* process 39 entries at a time */
                  if (j_idx == 39)
                  {
                     /* 39 * 24 = 936 + 10 header = 946 */
                     readBuffer2[0] = 0xb2;
                     readBuffer2[1] = 0xc3;

                     /* 39 entries */
                     readBuffer2[4] = 0x27;
                     readBuffer2[5] = 0x00;

                     sendto(ref_g2_sock,(char *)readBuffer2,946,0,
                            (struct sockaddr *)&fromDst4,
                            sizeof(struct sockaddr_in));

                     j_idx = 0;
                  }
               }

               if (j_idx != 0)
               {
                  k_idx = 10 + (j_idx * 24);
                  memcpy(tmp, (char *)&k_idx, 2);
                  readBuffer2[0] = tmp[0];
                  readBuffer2[1] = tmp[1] | 0xc0;

                  memcpy(tmp, (char *)&j_idx, 2);
                  readBuffer2[4] = tmp[0];
                  readBuffer2[5] = tmp[1];

                  sendto(ref_g2_sock,(char *)readBuffer2, k_idx, 0,
                         (struct sockaddr *)&fromDst4,
                         sizeof(struct sockaddr_in));
               }
            }
         }
         else
         /* linked repeaters request */
         if ((recvlen2 == 4) &&
             (readBuffer2[0] == 4) &&
             (readBuffer2[1] == 192) &&
             (readBuffer2[2] == 5) &&
             (readBuffer2[3] == 0))
         {
            unsigned short i_idx = 0;
            unsigned short j_idx = 0;
            unsigned short k_idx = 0;
            unsigned char tmp[2];
            unsigned short total = 0;

            pos = inbound_list.find(ip);
            if (pos != inbound_list.end())
            {
               inbound_ptr = (inbound *)pos->second;
               /* traceit("Remote station %s %s requested linked repeaters list\n", inbound_ptr->call, ip); */

               /* header is 8 bytes */

               /* reply type */
               readBuffer2[2] = 5;
               readBuffer2[3] = 1;

               /* we can have up to 3 linked systems */
               total = 3;
               memcpy(tmp, (char *)&total, 2);
               readBuffer2[6] = tmp[0];
               readBuffer2[7] = tmp[1];

               for (i = 0, i_idx = 0; i < 3;  i++, i_idx++)
               {
                  /* each entry has 20 bytes */
                  if (to_remote_g2[i].to_mod != ' ')
                  {
                     if (i == 0)
                        readBuffer2[8 + (20 * j_idx)] = 'A';
                     else
                     if (i == 1)
                        readBuffer2[8 + (20 * j_idx)] = 'B';
                     else
                     if (i == 2)
                        readBuffer2[8 + (20 * j_idx)] = 'C';

                     strcpy((char *)readBuffer2 + 9 + (20 * j_idx), to_remote_g2[i].to_call);
                     readBuffer2[16 + (20 * j_idx)] = to_remote_g2[i].to_mod;

                     readBuffer2[17 + (20 * j_idx)] = 0;
                     readBuffer2[18 + (20 * j_idx)] = 0;
                     readBuffer2[19 + (20 * j_idx)] = 0;
                     readBuffer2[20 + (20 * j_idx)] = 0x50;
                     readBuffer2[21 + (20 * j_idx)] = 0x04;
                     readBuffer2[22 + (20 * j_idx)] = 0x32;
                     readBuffer2[23 + (20 * j_idx)] = 0x4d;
                     readBuffer2[24 + (20 * j_idx)] = 0x9f;
                     readBuffer2[25 + (20 * j_idx)] = 0xdb;
                     readBuffer2[26 + (20 * j_idx)] = 0x0e;
                     readBuffer2[27 + (20 * j_idx)] = 0;

                     j_idx++;

                     if (j_idx == 39)
                     {
                        /* 20 bytes for each user, so 39 * 20 = 780 bytes + 8 bytes header = 788 */
                        readBuffer2[0] = 0x14;
                        readBuffer2[1] = 0xc3;

                        k_idx = i_idx - 38;
                        memcpy(tmp, (char *)&k_idx, 2);
                        readBuffer2[4] = tmp[0];
                        readBuffer2[5] = tmp[1];

                        sendto(ref_g2_sock,(char *)readBuffer2,788,0,
                               (struct sockaddr *)&fromDst4,
                               sizeof(struct sockaddr_in));

                        j_idx = 0;
                     }
                  }
               }

               if (j_idx != 0)
               {
                  k_idx = 8 + (j_idx * 20);
                  memcpy(tmp, (char *)&k_idx, 2);
                  readBuffer2[0] = tmp[0];
                  readBuffer2[1] = tmp[1] | 0xc0;

                  if (i_idx > j_idx)
                     k_idx = i_idx - j_idx;
                  else
                     k_idx = 0;

                  memcpy(tmp, (char *)&k_idx, 2);
                  readBuffer2[4] = tmp[0];
                  readBuffer2[5] = tmp[1];

                  sendto(ref_g2_sock,(char *)readBuffer2, 8 + (j_idx * 20), 0,
                         (struct sockaddr *)&fromDst4,
                         sizeof(struct sockaddr_in));
               }
            }
         }
         else
         /* connected user list request */
         if ((recvlen2 == 4) &&
             (readBuffer2[0] == 4) &&
             (readBuffer2[1] == 192) &&
             (readBuffer2[2] == 6) &&
             (readBuffer2[3] == 0))
         {
            unsigned short i_idx = 0;
            unsigned short j_idx = 0;
            unsigned short k_idx = 0;
            unsigned char tmp[2];
            unsigned short total = 0;

            pos = inbound_list.find(ip);
            if (pos != inbound_list.end())
            {
               inbound_ptr = (inbound *)pos->second;
               /* traceit("Remote station %s %s requested connected user list\n", inbound_ptr->call, ip); */

               /* header is 8 bytes */

               /* reply type */
               readBuffer2[2] = 6;
               readBuffer2[3] = 0;

               /* total connected users */
               total =  inbound_list.size();
               memcpy(tmp, (char *)&total, 2);
               readBuffer2[6] = tmp[0];
               readBuffer2[7] = tmp[1];

               for (pos = inbound_list.begin(), i_idx = 0; pos != inbound_list.end();  pos++, i_idx++)
               {
                  /* each entry has 20 bytes */
                  readBuffer2[8 + (20 * j_idx)] = ' ';
                  inbound_ptr = (inbound *)pos->second;

                  readBuffer2[8 + (20 * j_idx)] = inbound_ptr->mod;
                  strcpy((char *)readBuffer2 + 9 + (20 * j_idx), inbound_ptr->call);

                  readBuffer2[17 + (20 * j_idx)] = 0;
                  /* readBuffer2[18 + (20 * j_idx)] = 0; */ readBuffer2[18 + (20 * j_idx)] = inbound_ptr->client;
                  readBuffer2[19 + (20 * j_idx)] = 0;
                  readBuffer2[20 + (20 * j_idx)] = 0x0d;
                  readBuffer2[21 + (20 * j_idx)] = 0x4d;
                  readBuffer2[22 + (20 * j_idx)] = 0x37;
                  readBuffer2[23 + (20 * j_idx)] = 0x4d;
                  readBuffer2[24 + (20 * j_idx)] = 0x6f;
                  readBuffer2[25 + (20 * j_idx)] = 0x98;
                  readBuffer2[26 + (20 * j_idx)] = 0x04;
                  readBuffer2[27 + (20 * j_idx)] = 0;

                  j_idx++;

                  if (j_idx == 39)
                  {
                     /* 20 bytes for each user, so 39 * 20 = 788 bytes + 8 bytes header = 788 */
                     readBuffer2[0] = 0x14;
                     readBuffer2[1] = 0xc3;

                     k_idx = i_idx - 38;
                     memcpy(tmp, (char *)&k_idx, 2);
                     readBuffer2[4] = tmp[0];
                     readBuffer2[5] = tmp[1];

                     sendto(ref_g2_sock,(char *)readBuffer2,788,0,
                            (struct sockaddr *)&fromDst4,
                            sizeof(struct sockaddr_in));

                     j_idx = 0;
                  }
               }

               if (j_idx != 0)
               {
                  k_idx = 8 + (j_idx * 20);
                  memcpy(tmp, (char *)&k_idx, 2);
                  readBuffer2[0] = tmp[0];
                  readBuffer2[1] = tmp[1] | 0xc0;

                  if (i_idx > j_idx)
                     k_idx = i_idx - j_idx;
                  else
                     k_idx = 0;

                  memcpy(tmp, (char *)&k_idx, 2);
                  readBuffer2[4] = tmp[0];
                  readBuffer2[5] = tmp[1];

                  sendto(ref_g2_sock,(char *)readBuffer2, 8 + (j_idx * 20), 0,
                         (struct sockaddr *)&fromDst4,
                         sizeof(struct sockaddr_in));
               }
            }
         }
         else
         /* date request */
         if ((recvlen2 == 4) &&
             (readBuffer2[0] == 4) &&
             (readBuffer2[1] == 192) &&
             (readBuffer2[2] == 8) &&
             (readBuffer2[3] == 0))
         {
            time_t ltime;
            struct tm tm;

            pos = inbound_list.find(ip);
            if (pos != inbound_list.end())
            {
               inbound_ptr = (inbound *)pos->second;
               /* traceit("Remote station %s %s requested date\n", inbound_ptr->call, ip); */

               time(&ltime);
               localtime_r(&ltime,&tm);

               readBuffer2[0] = 34;
               readBuffer2[1] = 192;
               readBuffer2[2] = 8;
               readBuffer2[3] = 0;
               readBuffer2[4] = 0xb5;
               readBuffer2[5] = 0xae;
               readBuffer2[6] = 0x37;
               readBuffer2[7] = 0x4d;
               snprintf((char *)readBuffer2 + 8, 1024 - 1,
                        "20%02d/%02d/%02d %02d:%02d:%02d %5.5s",
                        tm.tm_year % 100, tm.tm_mon+1,tm.tm_mday,
                        tm.tm_hour,tm.tm_min,tm.tm_sec, 
                        (tzname[0] == NULL)?"     ":tzname[0]);

               sendto(ref_g2_sock,(char *)readBuffer2,34,0,
                      (struct sockaddr *)&fromDst4,
                      sizeof(struct sockaddr_in));
            }
         }
         else
         /* version request */
         if ((recvlen2 == 4) &&
             (readBuffer2[0] == 4) &&
             (readBuffer2[1] == 192) &&
             (readBuffer2[2] == 3) &&
             (readBuffer2[3] == 0))
         {
            pos = inbound_list.find(ip);
            if (pos != inbound_list.end())
            {
               inbound_ptr = (inbound *)pos->second;
               /* traceit("Remote station %s %s requested version\n", inbound_ptr->call, ip); */

               readBuffer2[0] = 9;
               readBuffer2[1] = 192;
               readBuffer2[2] = 3;
               readBuffer2[3] = 0;
               strncpy((char *)readBuffer2 + 4, VERSION, 4);
               readBuffer2[8] = 0;

               sendto(ref_g2_sock,(char *)readBuffer2,9,0,
                      (struct sockaddr *)&fromDst4,
                      sizeof(struct sockaddr_in));
            }
         }
         else
         /*** disconnect request arrived from remote dongle or a remote repeater ***/ 
         if ((recvlen2 == 5) &&
             (readBuffer2[0] == 5) &&
             (readBuffer2[1] == 0) &&
             (readBuffer2[2] == 24) &&
             /*** readBuffer2[3] == ... ***/
             (readBuffer2[4] == 0))
         {
            /* drop dongle user */
            pos = inbound_list.find(ip);
            if (pos != inbound_list.end())
            {
               inbound_ptr = (inbound *)pos->second;
               if (readBuffer2[3] == 0x00)
               {
                  /* reply with the same DISCONNECT */
                  sendto(ref_g2_sock,(char *)readBuffer2,5,0,
                         (struct sockaddr *)&fromDst4,
                         sizeof(struct sockaddr_in));

                  if (memcmp(inbound_ptr->call, "1NFO", 4) != 0)
                     traceit("Call %s disconnected\n", inbound_ptr->call);
                  free(pos->second);
                  pos->second = NULL;
                  inbound_list.erase(pos);
               }
            }

            /* drop link to remote repeater */
            /* find my local module */
            /* the value of readBuffer2[3] contains remote_mod and local_mod */
            /* example: readBuffer2[3] is 0x13 , that means remote_mod is B, local_mod is D */
            i = (readBuffer2[3] & 0x0F);

            // traceit("Disconnect request arrived from remote system for our local module %d\n", i);
            if ((i >= 0) && (i < 3))
            {
               if ((fromDst4.sin_addr.s_addr == to_remote_g2[i].toDst4.sin_addr.s_addr) &&
                   (to_remote_g2[i].type == 'p'))
               {
                  traceit("Module %c unlinked from [%s] mod %c\n",
                           to_remote_g2[i].from_mod,
                           to_remote_g2[i].to_call, to_remote_g2[i].to_mod);

                  sprintf(notify_msg, "%c_unlinked.dat_UNLINKED", to_remote_g2[i].from_mod);
                  audio_notify(notify_msg);

                  to_remote_g2[i].type = ' ';
                  to_remote_g2[i].to_call[0] = '\0';
                  memset(&(to_remote_g2[i].toDst4),0,sizeof(struct sockaddr_in));
                  to_remote_g2[i].from_mod = ' ';
                  to_remote_g2[i].to_mod = ' ';
                  to_remote_g2[i].countdown = 0; 
                  to_remote_g2[i].is_connected = false;
                  to_remote_g2[i].in_streamid[0] = 0x00;
                  to_remote_g2[i].in_streamid[1] = 0x00;
               }
            }
            print_status_file();
         }
         else
         /*** reply arrived to our link request ***/ 
         /*** link has been established ***/
         if ((recvlen2 == 5) &&
             (readBuffer2[0] == 5) &&
             (readBuffer2[1] == 0) &&
             (readBuffer2[2] == 24) &&
             /*** readBuffer2[3] == ... ***/
             (readBuffer2[4] == 0x83))
         {
            /* find my local module */
            /* the value of readBuffer2[3] contains remote_mod and local_mod */
            /* example: readBuffer2[3] is 0x01 , that means local_mod is A, remote_mod is B */
            i = (readBuffer2[3] >> 4);

            traceit("Reply arrived from remote system, link established for our local module %d\n", i);

            if ((i >= 0) && (i < 3))
            {
               if ((fromDst4.sin_addr.s_addr == to_remote_g2[i].toDst4.sin_addr.s_addr) &&
                   (to_remote_g2[i].type == 'p'))
               {
                  if (!to_remote_g2[i].is_connected)
                  {
                     to_remote_g2[i].is_connected = true;
                     traceit("Module %c linked to [%s] mod %c\n",
                           to_remote_g2[i].from_mod,
                           to_remote_g2[i].to_call, to_remote_g2[i].to_mod);

                     print_status_file();
                     tracing[i].last_time = time(NULL);  //VA3UV
                     strcpy(linked_remote_system, to_remote_g2[i].to_call);
                     space_p = strchr(linked_remote_system, ' ');
                     if (space_p)
                        *space_p = '\0';
                     sprintf(notify_msg, "%c_linked.dat_LINKED_%s_%c",
                         to_remote_g2[i].from_mod,
                         linked_remote_system,
                         to_remote_g2[i].to_mod);
                     audio_notify(notify_msg);
                  }
               }
            }
         }
         else
         /*** reply arrived to our link request ***/
         /*** link has failed ***/
         if ((recvlen2 == 5) &&
             (readBuffer2[0] == 5) &&
             (readBuffer2[1] == 0) &&
             (readBuffer2[2] == 24) &&
             /*** readBuffer2[3] == ... ***/
             (readBuffer2[4] == 0x05))
         {
            /* find my local module */
            /* the value of readBuffer2[3] contains remote_mod and local_mod */
            /* example: readBuffer2[3] is 0x01 , that means local_mod is A, remote_mod is B */
            i = (readBuffer2[3] >> 4);  

            traceit("Reply arrived from remote system, link FAILED for our local module %d\n", i);

            if ((i >= 0) && (i < 3))
            {
               if ((fromDst4.sin_addr.s_addr == to_remote_g2[i].toDst4.sin_addr.s_addr) &&
                   (to_remote_g2[i].type == 'p'))
               {
                  if (to_remote_g2[i].to_call[0] != '\0')
                  {
                     traceit("Link module %c to [%s] %c is rejected\n",
                              to_remote_g2[i].from_mod, to_remote_g2[i].to_call,
                              to_remote_g2[i].to_mod);

                     sprintf(notify_msg, "%c_failed_linked.dat_FAILED_TO_LINK",
                             to_remote_g2[i].from_mod);
                     audio_notify(notify_msg);

                     to_remote_g2[i].type = ' ';
                     to_remote_g2[i].to_call[0] = '\0';
                     memset(&(to_remote_g2[i].toDst4),0,sizeof(struct sockaddr_in));
                     to_remote_g2[i].from_mod = ' ';
                     to_remote_g2[i].to_mod = ' ';
                     to_remote_g2[i].countdown = 0;
                     to_remote_g2[i].is_connected = false;
                     to_remote_g2[i].in_streamid[0] = 0x00;
                     to_remote_g2[i].in_streamid[1] = 0x00;

                     print_status_file();
                  }
               }
            }
         }
         else
         /* remote system is requesting a link */
         if ((recvlen2 == 13) &&
             (readBuffer2[0] == 0x0d) &&
             (readBuffer2[1] == 0x00) &&
             (readBuffer2[2] == 0x18) &&
             /*** readBuffer2[3] == ... ***/
             (readBuffer2[4] == 0x03) &&
             (memcmp(readBuffer2 + 9, "22j ", 4) == 0))
         {
            ip_pos = ip_list.find(ip);
            if (ip_pos != ip_list.end())
               traceit("Incoming plus repeater link request from [%s], [%s], RL=%02x\n", 
                        ip_pos->first.c_str(), ip_pos->second.c_str(), readBuffer2[3]);
            else
               traceit("Incoming plus repeater link request from [%s], RL=%02x, not found in db\n", 
                        ip, readBuffer2[3]);

            /* find my local module */
            /* the value of readBuffer2[3] contains remote_mod and local_mod */
            /* example: readBuffer2[3] is 0x13 , that means remote_mod is B, local_mod is D */
            i = (readBuffer2[3] & 0x0F);  /* my local module */
 
            j = (readBuffer2[3] >> 4);   /* remote module */


            traceit("Remote system %s,module=%d,  requesting to link with our local module %d\n", ip, j, i);


            if ((i >= 0) && (i < 3) &&   /* local mocule A,B,C */ 
                (j >= 0) && (j < 4) &&   /* remote module A,B,C,D */
                (ip_pos != ip_list.end()))
            {
               if (to_remote_g2[i].to_mod == ' ')
               {
                  /* now it can be added as a repeater */
                  to_remote_g2[i].type = 'p';
                  strncpy(to_remote_g2[i].to_call, ip_pos->second.c_str(), CALL_SIZE);
                  to_remote_g2[i].to_call[CALL_SIZE] = '\0';
                  memcpy(&(to_remote_g2[i].toDst4), &fromDst4, sizeof(struct sockaddr_in));
                  // to_remote_g2[i].toDst4.sin_port = htons(RMT_REF_PORT);
                  
                  if (i == 0)
                     to_remote_g2[i].from_mod = 'A';
                  else
                  if (i == 1)
                     to_remote_g2[i].from_mod = 'B';
                  else
                  if (i == 2)
                     to_remote_g2[i].from_mod = 'C'; 


                  if (j == 0)
                     to_remote_g2[i].to_mod = 'A';
                  else
                  if (j == 1)
                     to_remote_g2[i].to_mod = 'B';
                  else
                  if (j == 2)
                     to_remote_g2[i].to_mod = 'C';
                  else
                  if (j == 3)
                     to_remote_g2[i].to_mod = 'D';

                  /* no duplicate assignments */
                  for (k = 0; k < 3; k++)
                  {
                     if (k == i)
                        continue;

                     if ((to_remote_g2[k].to_mod == to_remote_g2[i].to_mod) &&
                         (strcmp(to_remote_g2[k].to_call, to_remote_g2[i].to_call) == 0))
                        break;
                  }
                  if (k > 2)
                  {
                     to_remote_g2[i].countdown = TIMEOUT;
                     to_remote_g2[i].is_connected = true;
                     to_remote_g2[i].in_streamid[0] = 0x00;
                     to_remote_g2[i].in_streamid[1] = 0x00;

                     print_status_file();
                     tracing[i].last_time = time(NULL);

                     traceit("Module %c to [%s] %c linked\n",
                              to_remote_g2[i].from_mod,
                              to_remote_g2[i].to_call, to_remote_g2[i].to_mod);

                     strcpy(linked_remote_system, to_remote_g2[i].to_call);
                     space_p = strchr(linked_remote_system, ' ');
                     if (space_p)
                        *space_p = '\0';
                     sprintf(notify_msg, "%c_linked.dat_LINKED_%s_%c",
                         to_remote_g2[i].from_mod,
                         linked_remote_system,
                         to_remote_g2[i].to_mod);
                     audio_notify(notify_msg);

                     dplus_ack[0] = 0x05;
                     dplus_ack[1] = 0x00;
                     dplus_ack[2] = 0x18;
                     dplus_ack[3] = readBuffer2[3];
                     dplus_ack[4] = 0x83;

                     // fromDst4.sin_port = htons(RMT_REF_PORT);
                     for (j = 0; j < 3; j++)
                        sendto(ref_g2_sock, (char *)dplus_ack, 5,
                               0,(struct sockaddr *)&fromDst4,
                               sizeof(struct sockaddr_in));
                  }
                  else
                  {
                     traceit("Another local module %c is already linked to: [%s], %c\n",
                           to_remote_g2[k].from_mod,
                           to_remote_g2[i].to_call, to_remote_g2[i].to_mod);

                     dplus_ack[0] = 0x05;
                     dplus_ack[1] = 0x00;
                     dplus_ack[2] = 0x18;
                     dplus_ack[3] = readBuffer2[3];
                     dplus_ack[4] = 0x05;

                     // fromDst4.sin_port = htons(RMT_REF_PORT);
                     for (j = 0; j < 3; j++)
                        sendto(ref_g2_sock, (char *)dplus_ack, 5,
                            0,(struct sockaddr *)&fromDst4,
                            sizeof(struct sockaddr_in));

                     to_remote_g2[i].type = ' ';
                     to_remote_g2[i].to_call[0] = '\0';
                     memset(&(to_remote_g2[i].toDst4),0,sizeof(struct sockaddr_in));
                     to_remote_g2[i].from_mod = ' ';
                     to_remote_g2[i].to_mod = ' ';
                     to_remote_g2[i].countdown = 0;
                     to_remote_g2[i].is_connected = false;
                     to_remote_g2[i].in_streamid[0] = 0x00;
                     to_remote_g2[i].in_streamid[1] = 0x00;
                  }
               }
               else
               {
                  /*** is this link request a duplicate ? ***/
                  if ((((j == 0) && (to_remote_g2[i].to_mod == 'A')) ||
                       ((j == 1) && (to_remote_g2[i].to_mod == 'B')) ||
                       ((j == 2) && (to_remote_g2[i].to_mod == 'C')) ||
                       ((j == 3) && (to_remote_g2[i].to_mod == 'D'))) && 
                       (strcmp(to_remote_g2[i].to_call, ip_pos->second.c_str()) == 0))
                  {
                     /*** do nothing ***/
                     traceit("Duplicate link request...\n");
                  }
                  else
                  { 
                     /* send back a NAK */
                     traceit("Our local module %c is already linked to: [%s], %c\n",
                           to_remote_g2[i].from_mod,
                           to_remote_g2[i].to_call, to_remote_g2[i].to_mod);
                           
                     dplus_ack[0] = 0x05;
                     dplus_ack[1] = 0x00;
                     dplus_ack[2] = 0x18;
                     dplus_ack[3] = readBuffer2[3];
                     dplus_ack[4] = 0x05;

                     // fromDst4.sin_port = htons(RMT_REF_PORT);
                     for (j = 0; j < 3; j++)
                        sendto(ref_g2_sock, (char *)dplus_ack, 5,
                            0,(struct sockaddr *)&fromDst4,
                            sizeof(struct sockaddr_in));
                  }
               }
            }
            else
            {
               traceit("Invalid module specifications or IP not in db\n");
               dplus_ack[0] = 0x05;
               dplus_ack[1] = 0x00;
               dplus_ack[2] = 0x18;
               dplus_ack[3] = readBuffer2[3];
               dplus_ack[4] = 0x05;

               // fromDst4.sin_port = htons(RMT_REF_PORT);
               for (j = 0; j < 3; j++)
                  sendto(ref_g2_sock, (char *)dplus_ack, 5,
                         0,(struct sockaddr *)&fromDst4,
                         sizeof(struct sockaddr_in));
            }
         }
   
         /* Is it a repeater? update counter */
         for (i = 0; i < 3; i++)
         {
            if ((fromDst4.sin_addr.s_addr == to_remote_g2[i].toDst4.sin_addr.s_addr) &&
                (to_remote_g2[i].type == 'p'))
            {
               found = true;
               if (recvlen2 == 3)
                  to_remote_g2[i].countdown = TIMEOUT;
            }
         }

         /* Is it a dongle? update counter */
         pos = inbound_list.find(ip);
         if (pos != inbound_list.end())
         {
            inbound_ptr = (inbound *)pos->second;
            found = true;
            inbound_ptr->countdown = TIMEOUT;
            /*** ip is same, do not update port
            memcpy((char *)&(inbound_ptr->sin),(char *)&fromDst4, sizeof(struct sockaddr_in));
            ***/
         }

         if (!found)
         {
            /* 
               The incoming packet is not in the list of repeater connections.
               and it is not a connected dongle.
            */
            if ((recvlen2 == 5) &&
                (readBuffer2[0] == 5) &&
                (readBuffer2[1] == 0) &&
                (readBuffer2[2] == 24) &&
                (readBuffer2[3] == 0) &&
                (readBuffer2[4] == 1))
            {
               if ((inbound_list.size() + 1) > MAX_DONGLES)
                  traceit("Inbound DONGLE-p connection from %s but over the MAX_DONGLES limit of %d\n", 
                          ip, inbound_list.size());
               else
                  sendto(ref_g2_sock,(char *)readBuffer2,5,0,
                         (struct sockaddr *)&fromDst4,
                         sizeof(fromDst4));
            }
            else
            if ((recvlen2 == 28) &&
                (readBuffer2[0] == 28) &&
                (readBuffer2[1] == 192) &&
                (readBuffer2[2] == 4) &&
                (readBuffer2[3] == 0))
            {
               /* verify callsign */
               memcpy(call, readBuffer2 + 4, CALL_SIZE);
               call[CALL_SIZE] = '\0';
               for (i = 7; i > 0; i--)
               {
                  if (call[i] == '\0')
                     call[i] = ' ';
                  else
                     break;
               }

               if (memcmp(call, "1NFO", 4) != 0) 
                  traceit("Inbound DONGLE-p CALL=%s, ip=%s, DV=%.8s\n",
                           call, ip, readBuffer2 + 20);

               if ((inbound_list.size() + 1) > MAX_DONGLES)
                  traceit("Inbound DONGLE-p connection from %s but over the MAX_DONGLES limit of %d\n",
                          ip, inbound_list.size());
               else
               if (ONLY_ADMIN_LOGIN && (admin.find(call) == admin.end()))
                  traceit("Incoming call [%s] from %s not an ADMIN\n", call, ip);
               else
               if ((regexec(&preg, call, 0, NULL, 0) != 0) ||
                   (memcmp(call, OWNER, CALL_SIZE) == 0))
               {
                  traceit("Invalid dongle callsign: CALL=%s,ip=%s\n", call, ip);

                  readBuffer2[0] = 8;
                  readBuffer2[4] = 70;
                  readBuffer2[5] = 65;
                  readBuffer2[6] = 73;
                  readBuffer2[7] = 76;
                 
                  sendto(ref_g2_sock,(char *)readBuffer2,8,0,
                         (struct sockaddr *)&fromDst4,
                         sizeof(fromDst4));
               }
               else
               {
                  /* add the dongle to the inbound list */
                  inbound_ptr = (inbound *)malloc(sizeof(inbound));
                  if (inbound_ptr)
                  {
                     inbound_ptr->countdown = TIMEOUT;
                     memcpy((char *)&(inbound_ptr->sin),(char *)&fromDst4, sizeof(struct sockaddr_in));
                     strcpy(inbound_ptr->call, call);

                     inbound_ptr->mod = ' ';

                     if (memcmp(readBuffer2 + 20, "AP", 2) == 0)
                        inbound_ptr->client = 'A';  /* dvap */
                     else
                     if (memcmp(readBuffer2 + 20, "DV019999", 8) == 0)
                        inbound_ptr->client = 'H';  /* spot */
                     else
                        inbound_ptr->client = 'D';  /* dongle */
                   
                     insert_pair = inbound_list.insert(pair<string, inbound *>(ip, inbound_ptr));
                     if (insert_pair.second)
                     {
                        if (memcmp(inbound_ptr->call, "1NFO", 4) != 0)
                           traceit("new CALL=%s, DONGLE-p, ip=%s, users=%d\n",
                                   inbound_ptr->call,ip,inbound_list.size());

                        readBuffer2[0] = 8;
                        readBuffer2[4] = 79;
                        readBuffer2[5] = 75;
                        readBuffer2[6] = 82;
                        readBuffer2[7] = 87;

                        sendto(ref_g2_sock,(char *)readBuffer2,8,0,
                               (struct sockaddr *)&fromDst4,
                               sizeof(fromDst4));

                        print_status_file();

                     }
                     else
                     {
                        traceit("failed to add CALL=%s,ip=%s\n",inbound_ptr->call,ip);
                        free(inbound_ptr);
                        inbound_ptr = NULL;

                        readBuffer2[0] = 8;
                        readBuffer2[4] = 70;
                        readBuffer2[5] = 65;
                        readBuffer2[6] = 73;
                        readBuffer2[7] = 76;

                        sendto(ref_g2_sock,(char *)readBuffer2,8,0,
                               (struct sockaddr *)&fromDst4,
                               sizeof(fromDst4));
                     }
                  }
                  else
                  {
                     traceit("malloc() failed for call=%s,ip=%s\n",call,ip);

                     readBuffer2[0] = 8;
                     readBuffer2[4] = 70;
                     readBuffer2[5] = 65;
                     readBuffer2[6] = 73;
                     readBuffer2[7] = 76;

                     sendto(ref_g2_sock,(char *)readBuffer2,8,0,
                            (struct sockaddr *)&fromDst4,
                            sizeof(fromDst4));
                  }
               }
            }
         }

         if ( ((recvlen2 == 58) ||
               (recvlen2 == 29) ||
               (recvlen2 == 32)) &&
              (memcmp(readBuffer2 + 2, "DSVT", 4) == 0) &&
              ((readBuffer2[6] == 0x10) ||
               (readBuffer2[6] == 0x20)) &&
              (readBuffer2[10] == 0x20))
         {
            /* Is it one of the donglers or repeaters-reflectors */
            found = false;
            for (i = 0; i < 3; i++)
            {
               if ((fromDst4.sin_addr.s_addr == to_remote_g2[i].toDst4.sin_addr.s_addr) &&
                   (to_remote_g2[i].type == 'p'))
               {
                  to_remote_g2[i].countdown = TIMEOUT;
                  found = true;
               }
            }
            if (!found)
            {
               pos = inbound_list.find(ip);
               if (pos != inbound_list.end())
               {
                  inbound_ptr = (inbound *)pos->second;
                  inbound_ptr->countdown = TIMEOUT;
                  found = true;
               }
            }

            if ((recvlen2 == 58) && found)
            {
               memset(source_stn, ' ', 9); source_stn[8] = '\0';

               /* some bad hotspot programs out there using INCORRECT flag */
               if (readBuffer2[17] == 0x40)
                  readBuffer2[17] = 0x00;
               else
               if (readBuffer2[17] == 0x48)
                  readBuffer2[17] = 0x08;
               else
               if (readBuffer2[17] == 0x60)
                  readBuffer2[17] = 0x20;
               else
               if (readBuffer2[17] == 0x68)
                  readBuffer2[17] = 0x28;

               /* A reflector will send to us its own RPT1 */
               /* A repeater will send to us its own RPT1 */
               /* A dongleR will send to us our RPT1 */

               /* It is from a repeater-reflector, correct rpt1, rpt2 and re-compute pfcs */
               for (i = 0; i < 3; i++)
               {
                  if ((fromDst4.sin_addr.s_addr == to_remote_g2[i].toDst4.sin_addr.s_addr) &&
                      (to_remote_g2[i].type == 'p') &&
                      (
                       ((memcmp(readBuffer2 + 20, to_remote_g2[i].to_call, 7) == 0) &&
                        (readBuffer2[27] == to_remote_g2[i].to_mod))  ||
                       ((memcmp(readBuffer2 + 28, to_remote_g2[i].to_call, 7) == 0) &&
                        (readBuffer2[35] == to_remote_g2[i].to_mod))
                      ))
                  {
                     memcpy(&readBuffer2[20], OWNER, CALL_SIZE);
                     readBuffer2[27] = to_remote_g2[i].from_mod;
                     memcpy(&readBuffer2[36], "CQCQCQ  ", 8);

                     memcpy(source_stn, to_remote_g2[i].to_call, 8); source_stn[7] = to_remote_g2[i].to_mod;

                     break;
                  }
               } 

               if (i == 3)
               {
                  pos = inbound_list.find(ip);
                  if (pos != inbound_list.end())
                  {
                     inbound_ptr = (inbound *)pos->second;
                     memcpy(source_stn, inbound_ptr->call, 8);
                  }
               }

               /* somebody's crazy idea of having a personal callsign in RPT2 */
               /* we must set it to our gateway callsign */
               memcpy(&readBuffer2[28], OWNER, CALL_SIZE);
               readBuffer2[35] = 'G';
               readBuffer2[8] = 0x00;
               calcPFCS(readBuffer2 + 2, 56);

               /* At this point, all data have our RPT1 and RPT2 */

               i = -1;
               if (readBuffer2[27] == 'A')
                  i = 0;
               else
               if (readBuffer2[27] == 'B')
                  i = 1;
               else
               if (readBuffer2[27] == 'C')
                  i = 2;

               /* are we sure that RPT1 is our system? */
               if ((memcmp(readBuffer2 + 20, OWNER, 7) == 0) && (i >= 0))
               {
                  /* Last Heard */
                  if (memcmp(old_sid[i].sid, readBuffer2 + 14, 2) != 0)
                  {
                     if (QSO_DETAILS)
                        traceit("START from remote g2: streamID=%d,%d, flags=%02x:%02x:%02x, my=%.8s, sfx=%.4s, ur=%.8s, rpt1=%.8s, rpt2=%.8s, %d bytes fromIP=%s, source=%.8s\n",
                                 readBuffer2[14],readBuffer2[15],
                                 readBuffer2[17], readBuffer2[18], readBuffer2[19],
                                 &readBuffer2[44],
                                 &readBuffer2[52], &readBuffer2[36],
                                 &readBuffer2[20], &readBuffer2[28],
                                 recvlen2,inet_ntoa(fromDst4.sin_addr), source_stn);

                     // put user into tmp1
                     memcpy(tmp1, readBuffer2 + 44, 8); tmp1[8] = '\0';

                     // delete the user if exists
                     for (dt_lh_pos = dt_lh_list.begin(); dt_lh_pos != dt_lh_list.end();  dt_lh_pos++)
                     {
                        if (strcmp((char *)dt_lh_pos->second.c_str(), tmp1) == 0)
                        {
                           dt_lh_list.erase(dt_lh_pos);
                           break;
                        }
                     }
                     /* Limit?, delete oldest user */
                     if (dt_lh_list.size() == LH_MAX_SIZE)
                     {
                        dt_lh_pos = dt_lh_list.begin();
                        dt_lh_list.erase(dt_lh_pos);
                     }
                     // add user
                     time(&tnow);
                     sprintf(tmp2, "%ld=r%.6s%c%c", tnow, source_stn, source_stn[7], readBuffer2[27]);
                     dt_lh_list[tmp2] = tmp1;

                     memcpy(old_sid[i].sid, readBuffer2 + 14, 2);
                  }

                  /* send the data to the local gateway/repeater */
                  sendto(ref_g2_sock, (char *)readBuffer2 + 2,56,0,(struct sockaddr *)&toLocalg2,sizeof(struct sockaddr_in));

                  /* send the data to the donglers */
                  for (pos = inbound_list.begin(); pos != inbound_list.end(); pos++)
                  {
                     inbound_ptr = (inbound *)pos->second;
                     if (fromDst4.sin_addr.s_addr != inbound_ptr->sin.sin_addr.s_addr)
                     {
                        sendto(ref_g2_sock, (char *)readBuffer2, 58, 0,
                               (struct sockaddr *)&(inbound_ptr->sin),
                               sizeof(struct sockaddr_in));
                     }
                     else
                        inbound_ptr->mod = readBuffer2[27];
                  }

                  /* Is there another local module linked to the remote same ref mod ? */
                  /* If Yes, then multilink */
                  k = i + 1;

                  if (k < 3)
                  {
                     ml_from_ref_idx = 0;
                     streamid_raw = (readBuffer2[14] * 256U) + readBuffer2[15];

                     /* We can only enter this loop up to 2 times max */
                     for (j = k; j < 3; j++)  
                     {
                        /* it is a remote gateway, not a dongle user */
                        if ((fromDst4.sin_addr.s_addr == to_remote_g2[j].toDst4.sin_addr.s_addr) &&  
                            /* it is plus ref */
                            (to_remote_g2[j].type == 'p') &&
                            (memcmp(to_remote_g2[j].to_call, "REF", 3) == 0) &&
                            /* it is the same ref and ref module */
                            (memcmp(to_remote_g2[j].to_call, to_remote_g2[i].to_call, 8) == 0) &&
                            (to_remote_g2[j].to_mod == to_remote_g2[i].to_mod))
                        { 
                           /* send the packet to another module of our local repeater: this is multi-link */
                            
                           /* generate new packet */ 
                           memcpy(from_ref_torptr_brd, readBuffer2, 58);

                           /* different repeater module */
                           from_ref_torptr_brd[27] = to_remote_g2[j].from_mod;

                           /* assign new streamid */
                           streamid_raw ++;
                           if (streamid_raw == 0)
                              streamid_raw ++;
                           from_ref_torptr_brd[14] = streamid_raw / 256U;
                           from_ref_torptr_brd[15] = streamid_raw % 256U;

                           memcpy(from_ref_torptr_brd + 36, "CQCQCQ  ", 8);    

                           calcPFCS(from_ref_torptr_brd + 2, 56);

                           /* send the data to the local gateway/repeater */
                           sendto(ref_g2_sock, (char *)from_ref_torptr_brd + 2,56,0,
                                  (struct sockaddr *)&toLocalg2,sizeof(struct sockaddr_in));

                           /* save streamid for use with the audio packets that will arrive after this header */

                           ml_from_ref.ref_streamid[0] = readBuffer2[14];
                           ml_from_ref.ref_streamid[1] = readBuffer2[15];
                           ml_from_ref.rptr_streamid[ml_from_ref_idx][0] = from_ref_torptr_brd[14];
                           ml_from_ref.rptr_streamid[ml_from_ref_idx][1] = from_ref_torptr_brd[15];
                           ml_from_ref_idx ++;
                        }
                     }
                  }

                  /* send the data to the repeater/reflector that is linked to our RPT1 */
                   
                  /*** remember where it came from ***/
                  plus_crap[i].adr = fromDst4.sin_addr.s_addr;
                  plus_crap[i].streamid[0] = readBuffer2[14];
                  plus_crap[i].streamid[1] = readBuffer2[15];

                  if ((to_remote_g2[i].toDst4.sin_addr.s_addr != fromDst4.sin_addr.s_addr) &&
                     to_remote_g2[i].is_connected)
                  {
                     if ((memcmp(readBuffer2 + 44, OWNER, 7) != 0) &&         /* block repeater announcements */
                         (memcmp(readBuffer2 + 36, "CQCQCQ", 6) == 0) &&     /* CQ calls only */
                         ((readBuffer2[17] == 0x00)  ||                       /* normal */
                          (readBuffer2[17] == 0x08)  ||                       /* EMR */
                          (readBuffer2[17] == 0x20)  ||                       /* BK */
                          (readBuffer2[17] == 0x28)) &&                       /* EMR + BK */
                         (memcmp(readBuffer2 + 28, OWNER, 7) == 0) &&         /* rpt2 must be us */
                         (readBuffer2[35] == 'G'))
                     {
                        /*** SHIT games with this SHIT ***/
                        if (to_remote_g2[i].type == 'x')
                        {
                           to_remote_g2[i].in_streamid[0] = readBuffer2[14];
                           to_remote_g2[i].in_streamid[1] = readBuffer2[15];

                           /* inform XRF about the source */
                           readBuffer2[13] = to_remote_g2[i].from_mod;

                           memcpy((char *)readBuffer2 + 20, to_remote_g2[i].to_call, CALL_SIZE);
                           readBuffer2[27] = to_remote_g2[i].to_mod;
                           memcpy((char *)readBuffer2 + 28, to_remote_g2[i].to_call, CALL_SIZE);
                           readBuffer2[35] = 'G';
                           calcPFCS(readBuffer2 + 2, 56);

                           sendto(xrf_g2_sock, (char *)readBuffer2 + 2, 56, 0,
                                 (struct sockaddr *)&(to_remote_g2[i].toDst4),
                                  sizeof(struct sockaddr_in));
                        }
                        else
                        if (to_remote_g2[i].type == 'p')
                        {
                           /* we must NOT send an INVALID mycall to remote REF */
                           memcpy(call, readBuffer2 + 44, CALL_SIZE);
                           call[CALL_SIZE] = '\0';
                           if (valid_callsigns.find(call) == valid_callsigns.end())
                              traceit("Invalid mycall=[%s] will not be transmitted\n", call);
                           else
                           {
                              to_remote_g2[i].in_streamid[0] = readBuffer2[14];
                              to_remote_g2[i].in_streamid[1] = readBuffer2[15];

                              readBuffer2[11] = 0x00;
                              readBuffer2[12] = 0x01;
                              readBuffer2[13] = 0x02;
                              memcpy(readBuffer2 + 20, OWNER, CALL_SIZE);
                              readBuffer2[27] = to_remote_g2[i].from_mod;
                              memcpy(readBuffer2 + 28, OWNER, CALL_SIZE);
                              readBuffer2[35] = 'G';
                              calcPFCS(readBuffer2 + 2, 56);

                              sendto(ref_g2_sock, (char *)readBuffer2, 58, 0,
                                     (struct sockaddr *)&(to_remote_g2[i].toDst4),
                                     sizeof(struct sockaddr_in));
                           }
                        }
                        else
                        if (to_remote_g2[i].type == 'd')
                        {
                           to_remote_g2[i].in_streamid[0] = readBuffer2[14];
                           to_remote_g2[i].in_streamid[1] = readBuffer2[15];

                           memcpy(ref_2_dcs[i].mycall, readBuffer2 + 44, 8);
                           memcpy(ref_2_dcs[i].sfx, readBuffer2 + 52, 4);
                           ref_2_dcs[i].dcs_rptr_seq = 0;
                        }
                        /*** SHIT SHIT end ***/
                     }
                  }
               }
            }
            else
            if (found)
            {
               readBuffer2[8] = 0x00;

               for (i = 0; i < 3; i++)
               {
                  if ((plus_crap[i].adr == fromDst4.sin_addr.s_addr) &&
                      (memcmp(plus_crap[i].streamid, readBuffer2 + 14, 2) == 0))
                  {
                     /* send the data to the local gateway/repeater */
                     sendto(ref_g2_sock, (char *)readBuffer2 + 2,27,0,(struct sockaddr *)&toLocalg2,sizeof(struct sockaddr_in));

                     /* send the data to the donglers */
                     for (pos = inbound_list.begin(); pos != inbound_list.end(); pos++)
                     {
                        inbound_ptr = (inbound *)pos->second;
                        if (fromDst4.sin_addr.s_addr != inbound_ptr->sin.sin_addr.s_addr)
                        {
                           sendto(ref_g2_sock, (char *)readBuffer2, 29, 0,
                                  (struct sockaddr *)&(inbound_ptr->sin),
                                  sizeof(struct sockaddr_in));
                        }
                     }

                     /* do we have to multilink ? */
                     if (memcmp(ml_from_ref.ref_streamid, readBuffer2 + 14, 2) == 0)
                     {
                        memcpy(from_ref_torptr_brd, readBuffer2, 29);

                        if ((ml_from_ref.rptr_streamid[0][0] != 0x00) ||
                            (ml_from_ref.rptr_streamid[0][1] != 0x00))
                        {
                           from_ref_torptr_brd[14] = ml_from_ref.rptr_streamid[0][0];
                           from_ref_torptr_brd[15] = ml_from_ref.rptr_streamid[0][1];
                           sendto(ref_g2_sock, (char *)from_ref_torptr_brd + 2,27,0,
                                  (struct sockaddr *)&toLocalg2,sizeof(struct sockaddr_in));
                        }

                        if ((ml_from_ref.rptr_streamid[1][0] != 0x00) ||
                            (ml_from_ref.rptr_streamid[1][1] != 0x00))
                        {
                           from_ref_torptr_brd[14] = ml_from_ref.rptr_streamid[1][0];
                           from_ref_torptr_brd[15] = ml_from_ref.rptr_streamid[1][1];
                           sendto(ref_g2_sock, (char *)from_ref_torptr_brd + 2,27,0,
                                  (struct sockaddr *)&toLocalg2,sizeof(struct sockaddr_in));
                        }

                        if ((readBuffer2[16] & 0x40) != 0)
                        {
                           ml_from_ref.ref_streamid[0] = ml_from_ref.ref_streamid[1] = 0x00;
                           ml_from_ref.rptr_streamid[0][0] = ml_from_ref.rptr_streamid[0][1] = 0x00;
                           ml_from_ref.rptr_streamid[1][0] = ml_from_ref.rptr_streamid[1][1] = 0x00;
                           ml_from_ref_idx = 0;
                        }
                     }

                     break;
                  }
               }

               for (i = 0; i < 3; i++)
               {
                  if ((to_remote_g2[i].is_connected) &&
                      (to_remote_g2[i].toDst4.sin_addr.s_addr != fromDst4.sin_addr.s_addr) &&
                      (plus_crap[i].adr == fromDst4.sin_addr.s_addr) &&
                      (memcmp(to_remote_g2[i].in_streamid, readBuffer2 + 14, 2) == 0))
                  {
                     if (to_remote_g2[i].type == 'x')
                     {
                        /* inform XRF about the source */
                        readBuffer2[13] = to_remote_g2[i].from_mod;

                        sendto(xrf_g2_sock, (char *)readBuffer2 + 2, 27, 0,
                               (struct sockaddr *)&(to_remote_g2[i].toDst4),
                               sizeof(struct sockaddr_in));
                     }
                     else
                     if (to_remote_g2[i].type == 'p')
                     {
                        /*** SHIT SHIT start ***/
                        readBuffer2[11] = 0x00;
                        readBuffer2[12] = 0x01;
                        readBuffer2[13] = 0x02;
                        /*** SHIT SHIT start ***/

                        sendto(ref_g2_sock, (char *)readBuffer2, 29,
                               0,(struct sockaddr *)&(to_remote_g2[i].toDst4),
                               sizeof(struct sockaddr_in));
                     }
                     else
                     if (to_remote_g2[i].type == 'd')
                     {                
                        memset(dcs_buf, 0x00, 600);
                        dcs_buf[0] = dcs_buf[1] = dcs_buf[2] = '0';
                        dcs_buf[3] = '1';
                        dcs_buf[4] = dcs_buf[5] = dcs_buf[6] = 0x00;
                        memcpy(dcs_buf + 7, to_remote_g2[i].to_call, 8);
                        dcs_buf[14] = to_remote_g2[i].to_mod;
                        memcpy(dcs_buf + 15, OWNER, 8);
                        dcs_buf[22] = to_remote_g2[i].from_mod;
                        memcpy(dcs_buf + 23, "CQCQCQ  ", 8);
                        memcpy(dcs_buf + 31, ref_2_dcs[i].mycall, 8);
                        memcpy(dcs_buf + 39, ref_2_dcs[i].sfx, 4);
                        dcs_buf[43] = readBuffer2[14];  /* streamid0 */
                        dcs_buf[44] = readBuffer2[15];  /* streamid1 */
                        dcs_buf[45] = readBuffer2[16];  /* cycle sequence */
                        memcpy(dcs_buf + 46, readBuffer2 + 17, 12);

                        dcs_buf[58] = (ref_2_dcs[i].dcs_rptr_seq >> 0)  & 0xff;
                        dcs_buf[59] = (ref_2_dcs[i].dcs_rptr_seq >> 8)  & 0xff;
                        dcs_buf[60] = (ref_2_dcs[i].dcs_rptr_seq >> 16) & 0xff;

                        ref_2_dcs[i].dcs_rptr_seq ++;

                        dcs_buf[61] = 0x01;
                        dcs_buf[62] = 0x00;

                        sendto(dcs_g2_sock, dcs_buf, 100, 0,
                                  (struct sockaddr *)&(to_remote_g2[i].toDst4),
                                  sizeof(to_remote_g2[i].toDst4));
                     }

                     if ((readBuffer2[16] & 0x40) != 0)
                     {
                        to_remote_g2[i].in_streamid[0] = 0x00;
                        to_remote_g2[i].in_streamid[1] = 0x00;
                     }
                     break;
                  }
               }

               if ((readBuffer2[16] & 0x40) != 0)
               {
                  for (i = 0; i < 3; i++)
                  {
                     if (memcmp(old_sid[i].sid, readBuffer2 + 14, 2) == 0)
                     {
                        if (QSO_DETAILS)
                           traceit("END from remote g2: streamID=%d,%d, %d bytes from IP=%s\n",
                                    readBuffer2[14],readBuffer2[15],recvlen2,inet_ntoa(fromDst4.sin_addr));
                        memset(old_sid[i].sid, 0x00, 2);
                        break;
                     }
                  }

                  for (i = 0; i < 3; i++)
                  {
                     if ((plus_crap[i].adr == fromDst4.sin_addr.s_addr) &&
                         (memcmp(plus_crap[i].streamid, readBuffer2 + 14, 2) == 0))
                     {
                        plus_crap[i].adr = 0;
                        plus_crap[i].streamid[0] = plus_crap[i].streamid[1] = 0x00;
                        break;
                     }
                  }
               }
            }
         }
         FD_CLR (ref_g2_sock,&fdset);
      }

      if (FD_ISSET(dcs_g2_sock, &fdset))
      {
         fromlen = sizeof(struct sockaddr_in);
         recvlen2 = recvfrom(dcs_g2_sock,(char *)dcs_buf,1000,
                            0,(struct sockaddr *)&fromDst4,&fromlen);

         strncpy(ip, inet_ntoa(fromDst4.sin_addr),IP_SIZE);
         ip[IP_SIZE] = '\0';

         /* header, audio */
         if ((dcs_buf[0] == '0') && (dcs_buf[1] == '0') &&
             (dcs_buf[2] == '0') && (dcs_buf[3] == '1'))
         {
            if (recvlen2 == 100)
            {
               memset(source_stn, ' ', 9); source_stn[8] = '\0';

               /* find out our local module */
               for (i = 0; i < 3; i++)
               {
                  if ((to_remote_g2[i].is_connected) &&
                      (fromDst4.sin_addr.s_addr = to_remote_g2[i].toDst4.sin_addr.s_addr) &&
                      (memcmp(dcs_buf + 7, to_remote_g2[i].to_call, 7) == 0) &&
                      (to_remote_g2[i].to_mod == dcs_buf[14]))
                  {
                     memcpy(source_stn, to_remote_g2[i].to_call, 8); source_stn[7] = to_remote_g2[i].to_mod;
                     break;
                  }
               }

               /* Is it our local module */
               if (i < 3)
               {
                  /* Last Heard */
                  if (memcmp(old_sid[i].sid, dcs_buf + 43, 2) != 0)
                  {
                     if (QSO_DETAILS)
                        traceit("START from dcs: streamID=%d,%d, my=%.8s, sfx=%.4s, ur=%.8s, rpt1=%.8s, rpt2=%.8s, %d bytes fromIP=%s, source=%.8s\n",
                                dcs_buf[43],dcs_buf[44],
                                &dcs_buf[31],
                                &dcs_buf[39], &dcs_buf[23],
                                &dcs_buf[7], &dcs_buf[15],
                                recvlen2,inet_ntoa(fromDst4.sin_addr), source_stn);

                     // put user into tmp1
                     memcpy(tmp1, dcs_buf + 31, 8); tmp1[8] = '\0';

                     // delete the user if exists
                     for (dt_lh_pos = dt_lh_list.begin(); dt_lh_pos != dt_lh_list.end();  dt_lh_pos++)
                     {
                        if (strcmp((char *)dt_lh_pos->second.c_str(), tmp1) == 0)
                        {
                           dt_lh_list.erase(dt_lh_pos);
                           break;
                        }
                     }
                     /* Limit?, delete oldest user */
                     if (dt_lh_list.size() == LH_MAX_SIZE)
                     {
                        dt_lh_pos = dt_lh_list.begin();
                        dt_lh_list.erase(dt_lh_pos);
                     }
                     // add user
                     time(&tnow);
                     sprintf(tmp2, "%ld=r%.6s%c%c", tnow, source_stn, source_stn[7], to_remote_g2[i].from_mod);
                     dt_lh_list[tmp2] = tmp1;

                     memcpy(old_sid[i].sid, dcs_buf + 43, 2);

                  }

                  to_remote_g2[i].countdown = TIMEOUT;

                  /* new stream ? */
                  if ((to_remote_g2[i].in_streamid[0] != dcs_buf[43]) ||
                      (to_remote_g2[i].in_streamid[1] != dcs_buf[44]))
                  {
                     to_remote_g2[i].in_streamid[0] = dcs_buf[43];
                     to_remote_g2[i].in_streamid[1] = dcs_buf[44];
                     dcs_seq[i] = 0xff;

                     /* generate our header */

                     readBuffer2[0] = (unsigned char)(58 & 0xFF);
                     readBuffer2[1] = (unsigned char)(58 >> 8 & 0x1F);
                     readBuffer2[1] = (unsigned char)(readBuffer2[1] | 0xFFFFFF80);
                     memcpy(readBuffer2 + 2, "DSVT", 4);
                     readBuffer2[6] = 0x10;
                     readBuffer2[7] = 0x00;
                     readBuffer2[8] = 0x00;
                     readBuffer2[9] = 0x00;
                     readBuffer2[10] = 0x20;
                     readBuffer2[11] = 0x00;
                     readBuffer2[12] = 0x01;
                     if (to_remote_g2[i].from_mod == 'A')
                        readBuffer2[13] = 0x03;
                     else
                     if (to_remote_g2[i].from_mod == 'B')
                        readBuffer2[13] = 0x01;
                     else
                        readBuffer2[13] = 0x02;
                     readBuffer2[14] = dcs_buf[43];
                     readBuffer2[15] = dcs_buf[44];
                     readBuffer2[16] = 0x80;
                     readBuffer2[17] = readBuffer2[18] = readBuffer2[19] = 0x00;
                     memcpy(readBuffer2 + 20, OWNER, 8);
                     readBuffer2[27] = to_remote_g2[i].from_mod;
                     memcpy(readBuffer2 + 28, OWNER, 8);
                     readBuffer2[35] = 'G';
                     memcpy(readBuffer2 + 36, "CQCQCQ  ", 8);
                     memcpy(readBuffer2 + 44, dcs_buf + 31, 8);
                     memcpy(readBuffer2 + 52, dcs_buf + 39, 4);
                     calcPFCS(readBuffer2 + 2, 56);

                     /* send the header to the local gateway/repeater */
                     for (j = 0; j < 2; j++)
                        sendto(dcs_g2_sock, (char *)readBuffer2 + 2, 56,0,
                            (struct sockaddr *)&toLocalg2,sizeof(struct sockaddr_in));

                     /* send the data to the donglers */
                     for (pos = inbound_list.begin(); pos != inbound_list.end(); pos++)
                     {
                        inbound_ptr = (inbound *)pos->second;
                        for (j = 0; j < 5; j++)
                        {
                           sendto(ref_g2_sock, (char *)readBuffer2, 58, 0,
                                  (struct sockaddr *)&(inbound_ptr->sin),
                                  sizeof(struct sockaddr_in));
                        }
                     }
                  }

                  if ((to_remote_g2[i].in_streamid[0] == dcs_buf[43]) &&
                      (to_remote_g2[i].in_streamid[1] == dcs_buf[44]) &&
                      (dcs_seq[i] != dcs_buf[45]))
                  {
                     dcs_seq[i] = dcs_buf[45];

                     readBuffer2[0] = (unsigned char)(29 & 0xFF);
                     readBuffer2[1] = (unsigned char)(29 >> 8 & 0x1F);
                     readBuffer2[1] = (unsigned char)(readBuffer2[1] | 0xFFFFFF80);
                     memcpy(readBuffer2 + 2, "DSVT", 4);
                     readBuffer2[6] = 0x20;
                     readBuffer2[7] = 0x00;
                     readBuffer2[8] = 0x00;
                     readBuffer2[9] = 0x00;
                     readBuffer2[10] = 0x20;
                     readBuffer2[11] = 0x00;
                     readBuffer2[12] = 0x01;
                     if (to_remote_g2[i].from_mod == 'A')
                        readBuffer2[13] = 0x03;
                     else
                     if (to_remote_g2[i].from_mod == 'B')
                        readBuffer2[13] = 0x01;
                     else
                        readBuffer2[13] = 0x02;
                     readBuffer2[14] = dcs_buf[43];
                     readBuffer2[15] = dcs_buf[44];
                     readBuffer2[16] = dcs_buf[45];
                     memcpy(readBuffer2 + 17, dcs_buf + 46, 12);

                     /* send the data to the local gateway/repeater */
                     sendto(dcs_g2_sock, (char *)readBuffer2 + 2, 27,0,
                            (struct sockaddr *)&toLocalg2,sizeof(struct sockaddr_in));

                     /* send the data to the donglers */
                     for (pos = inbound_list.begin(); pos != inbound_list.end(); pos++)
                     {
                        inbound_ptr = (inbound *)pos->second;
                        sendto(ref_g2_sock, (char *)readBuffer2, 29, 0,
                               (struct sockaddr *)&(inbound_ptr->sin),
                               sizeof(struct sockaddr_in));
                     }

                     if ((dcs_buf[45] & 0x40) != 0)
                     {
                        memset(old_sid[i].sid, 0x00, 2);

                        if (QSO_DETAILS)
                           traceit("END from dcs: streamID=%d,%d, %d bytes from IP=%s\n",
                                   dcs_buf[43],dcs_buf[44], recvlen2,inet_ntoa(fromDst4.sin_addr));

                        to_remote_g2[i].in_streamid[0] = 0x00;
                        to_remote_g2[i].in_streamid[1] = 0x00;
                        dcs_seq[i] = 0xff;
                     }
                  }
               }
            }
         }
         else
         if ((dcs_buf[0] == 'E') && (dcs_buf[1] == 'E') &&
             (dcs_buf[2] == 'E') && (dcs_buf[3] == 'E'))
            ;
         else
         if (recvlen2 == 35)
            ;
         else
         /* is this a keepalive 22 bytes */
         if (recvlen2 == 22)
         {
            i = -1;
            if (dcs_buf[17] == 'A')
               i = 0;
            else
            if (dcs_buf[17] == 'B')
               i = 1;
            else
            if (dcs_buf[17] == 'C')
               i = 2;

            /* It is one of our valid repeaters */

            // VA3UV - changed OWNER from 8 to 7

            if ((i >= 0) && (memcmp(dcs_buf + 9, OWNER, 7) == 0))
            {
               /* is that the remote system that we asked to connect to? */
               if ((fromDst4.sin_addr.s_addr == to_remote_g2[i].toDst4.sin_addr.s_addr) &&
                   (to_remote_g2[i].toDst4.sin_port == htons(RMT_DCS_PORT)) &&
                   (memcmp(to_remote_g2[i].to_call, dcs_buf, 7) == 0) &&
                   (to_remote_g2[i].to_mod == dcs_buf[7]))
               {
                  if (!to_remote_g2[i].is_connected)
                  {
                     to_remote_g2[i].is_connected = true;
                     traceit("Connected from: %.*s\n", 8, dcs_buf);
                     print_status_file();

                     tracing[i].last_time = time(NULL); //VA3UV

                     strcpy(linked_remote_system, to_remote_g2[i].to_call);
                     space_p = strchr(linked_remote_system, ' ');
                     if (space_p)
                        *space_p = '\0';
                     sprintf(notify_msg, "%c_linked.dat_LINKED_%s_%c",
                            to_remote_g2[i].from_mod,
                            linked_remote_system,
                            to_remote_g2[i].to_mod);
                     audio_notify(notify_msg);
                  }
                  to_remote_g2[i].countdown = TIMEOUT;
               }
            }
         }
         /* is this a reply to our link/unlink request: 14 bytes */
         else
         if (recvlen2 == 14)
         {
            i = -1;
            if (dcs_buf[8] == 'A')
               i = 0;
            else
            if (dcs_buf[8] == 'B')
               i = 1;
            else
            if (dcs_buf[8] == 'C')
               i = 2;

            /* It is one of our valid repeaters */
            if ((i >= 0) && (memcmp(dcs_buf, OWNER, 8) == 0))
            {
               /* It is from a remote that we contacted */
               if ((fromDst4.sin_addr.s_addr == to_remote_g2[i].toDst4.sin_addr.s_addr) &&
                   (to_remote_g2[i].toDst4.sin_port == htons(RMT_DCS_PORT)) &&
                   (to_remote_g2[i].from_mod == dcs_buf[8]))
               {
                  if ((to_remote_g2[i].to_mod == dcs_buf[9]) &&
                      (memcmp(dcs_buf + 10, "ACK", 3) == 0))
                  {
                     to_remote_g2[i].countdown = TIMEOUT;
                     if (!to_remote_g2[i].is_connected)
                     {
                        tracing[i].last_time = time(NULL);
                        to_remote_g2[i].is_connected = true;
                        traceit("Connected from: %.*s\n", 8, to_remote_g2[i].to_call);
                        print_status_file();

                        tracing[i].last_time = time(NULL); //VA3UV

                        strcpy(linked_remote_system, to_remote_g2[i].to_call);
                        space_p = strchr(linked_remote_system, ' ');
                        if (space_p)
                           *space_p = '\0';
                        sprintf(notify_msg, "%c_linked.dat_LINKED_%s_%c",
                            to_remote_g2[i].from_mod,
                            linked_remote_system,
                            to_remote_g2[i].to_mod);
                        audio_notify(notify_msg);
                     }
                  }
                  else
                  if (memcmp(dcs_buf + 10, "NAK", 3) == 0)
                  {
                     traceit("Link module %c to [%s] %c is unlinked\n",
                              to_remote_g2[i].from_mod, to_remote_g2[i].to_call,
                              to_remote_g2[i].to_mod);

                     sprintf(notify_msg, "%c_failed_linked.dat_UNLINKED",
                             to_remote_g2[i].from_mod);
                     audio_notify(notify_msg);

                     //v3.18

                     sprintf(df_b, "/dstar/tmp/blocklinking-%c", tolower(to_remote_g2[i].from_mod));
                     unlink(df_b);
                     to_remote_g2[i].to_call[0] = '\0';
                     memset(&(to_remote_g2[i].toDst4),0,sizeof(struct sockaddr_in));
                     to_remote_g2[i].from_mod = ' ';
                     to_remote_g2[i].to_mod = ' ';
                     to_remote_g2[i].countdown = 0;
                     to_remote_g2[i].is_connected = false;
                     to_remote_g2[i].in_streamid[0] = 0x00;
                     to_remote_g2[i].in_streamid[1] = 0x00;

                     print_status_file();
                  }
               }
            }
         }
         FD_CLR (dcs_g2_sock,&fdset);
      }

      if (FD_ISSET(rptr_sock, &fdset))
      {
         fromlen = sizeof(struct sockaddr_ll);
         recvlen = recvfrom(rptr_sock,(char *)readBuffer,1024,
                            0,(struct sockaddr *)&sll,&fromlen);

         if (sll.sll_pkttype == PACKET_HOST) 
         {
            ip_hdr = (struct iphdr *)(readBuffer);
            if ((ip_hdr->protocol == IPPROTO_UDP) &&
                !(ntohs(ip_hdr->frag_off) & IP_MF) &&
                (ip_hdr->version == 4) &&
                (ip_hdr->daddr == internal_daddr))
            {
               udp_hdr = (struct udphdr*)(readBuffer + ip_hdr->ihl*4);
               if ((udp_hdr->source == RP2C_PORT) &&
                   (udp_hdr->dest == G2_INTERNAL_PORT))
               {
                  udp_payload_len = ntohs(ip_hdr->tot_len) - ip_hdr->ihl*4 - sizeof(struct udphdr);
                  udp_payload = (u_char *)(readBuffer + ip_hdr->ihl*4 + sizeof(struct udphdr));

                  if ( ((udp_payload_len == 58) || 
                        (udp_payload_len == 29) || 
                        (udp_payload_len == 32)) &&
                       (udp_payload[6] == 0x73) &&
                       (udp_payload[7] == 0x12) &&
                       ((memcmp(udp_payload,"DSTR", 4) == 0) || (memcmp(udp_payload,"CCS_", 4) == 0)) &&
                       (udp_payload[10] == 0x20) &&
                       (udp_payload[8] == 0x00) &&     
                       ((udp_payload[9] == 0x30) || 
                        (udp_payload[9] == 0x13) ||
                        (udp_payload[9] == 0x16)) )
                  {
                     if (udp_payload_len == 58)
                     {
                        if (QSO_DETAILS)
                           traceit("START from rptr: cntr=%02x %02x, streamID=%d,%d, flags=%02x:%02x:%02x, my=%.8s, sfx=%.4s, ur=%.8s, rpt1=%.8s, rpt2=%.8s, %d bytes\n",
                           udp_payload[4], udp_payload[5],
                           udp_payload[14], udp_payload[15],
                           udp_payload[17], udp_payload[18], udp_payload[19],
                           udp_payload + 44, udp_payload + 52, udp_payload + 36,
                           udp_payload + 28, udp_payload + 20, udp_payload_len);

                        i = -1;
                        uv_rf_module = '\0';

                        if (udp_payload[35] == 'A')
                        {
                           i = 0;
                           uv_rf_module = 'A';
                        }
                        else
                        if (udp_payload[35] == 'B')
                        {  
                           i = 1;
                           uv_rf_module = 'B';
                        }
                        else
                        if (udp_payload[35] == 'C')
                        {
                           i = 2;
                           uv_rf_module = 'C';
                        }
                        /* save mycall */
                        memcpy(call, udp_payload + 44, 8);
                        call[8] = '\0';

                        /* good band, normal packet */
                        if ((i >= 0) &&
                            ((udp_payload[17] == 0x00) ||
                             (udp_payload[17] == 0x08) ||
                             (udp_payload[17] == 0x20) ||
                             (udp_payload[17] == 0x28)))
                        {
                           /* dtmf stuff */
                           dtmf_last_frame[i] = 0;
                           dtmf_counter[i] = 0;
                           memset(dtmf_buf[i], 0, sizeof(dtmf_buf[i]));
                           dtmf_buf_count[i] = 0;
                           memcpy(dtmf_mycall[i], udp_payload + 44, 8);
                           dtmf_mycall[i][8] = '\0';

                           new_group[i] = true;
                           GPS_seen[i] = false;

                           /* Last Heard */

                           //put user into tmp1
                           memcpy(tmp1, udp_payload + 44, 8); tmp1[8] = '\0';

                           // delete the user if exists
                           for (dt_lh_pos = dt_lh_list.begin(); dt_lh_pos != dt_lh_list.end();  dt_lh_pos++)
                           {
                              if (strcmp((char *)dt_lh_pos->second.c_str(), tmp1) == 0)
                              {
                                 dt_lh_list.erase(dt_lh_pos);
                                 break;
                              }
                           }
                           /* Limit?, delete oldest user */
                           if (dt_lh_list.size() == LH_MAX_SIZE)
                           {
                              dt_lh_pos = dt_lh_list.begin();
                              dt_lh_list.erase(dt_lh_pos);
                           }
                           /* add user */
                           time(&tnow);
                           if (memcmp(udp_payload,"CCS_", 4) == 0)
                              sprintf(tmp2, "%ld=r%.7s%c", tnow, "-->CCS ", udp_payload[35]);
                           else
                              sprintf(tmp2, "%ld=l%.8s", tnow, udp_payload + 28);
                           dt_lh_list[tmp2] = tmp1;

                           memcpy(udp_payload, "DSTR", 4);

                           tracing[i].streamid[0] = udp_payload[14];
                           tracing[i].streamid[1] = udp_payload[15];
                           tracing[i].last_time = time(NULL);
                        }

                        /* good band, normal packet, routing? */
                        if ((memcmp(udp_payload + 36, "CQCQCQ", 6) != 0) && (i >= 0) &&
                            ((udp_payload[17] == 0x00) ||
                             (udp_payload[17] == 0x08) ||
                             (udp_payload[17] == 0x20) ||
                             (udp_payload[17] == 0x28)))
                        {
                           if ((memcmp(udp_payload + 36, OWNER, 7) != 0) &&
                               (udp_payload[43] == LINK_CODE) &&
                                (memcmp(udp_payload + 20, OWNER, 7) == 0) &&
                                (udp_payload[27] == 'G'))
                           {
                              //traceit("I am here\n");
                              //traceit("ONLY_LINK_UNLINK_temp is %i\n", ONLY_LINK_UNLINK_temp);

                              // if ONLY_LINK_UNLINK = true; this means that only the named user can link
                              // if ONLY_LINK_UNLINK = false; then the specificed users can NOT link

                              if (ONLY_LINK_UNLINK && 
                                  (link_unlink_user.find(call) == link_unlink_user.end()))
                              {
                                 traceit("link request denied, unauthorized rf user [%s]\n", call);
                              }
                              else

                                  /* VA3UV - v3.12 - added check to make sure user callsign is valid before allowing link / unlink */

                              if (valid_callsigns.find(call) == valid_callsigns.end())
                                 traceit("Invalid mycall=[%s] rejecting link / unlink request\n", call);

                              else

                              if (!ONLY_LINK_UNLINK &&
                                  (link_unlink_user.find(call) != link_unlink_user.end()))

                              {
                                 traceit("link request denied - here, unauthorized rf user [%s]\n", call);
                              }
                              
                              else
                              
                              //
                              {
                                 memset(temp_repeater, ' ', CALL_SIZE);
                                 memcpy(temp_repeater, udp_payload + 36, CALL_SIZE - 2);
                                 temp_repeater[CALL_SIZE] = '\0';

                                 if ((to_remote_g2[i].to_call[0] == '\0') ||   /* not linked */
                                     ((to_remote_g2[i].to_call[0] != '\0') &&  /* waiting for a link reply that may never arrive */ 
                                     !to_remote_g2[i].is_connected))

                                    g2link(udp_payload[35], temp_repeater, udp_payload[42]);
                                 else
                                 if (to_remote_g2[i].is_connected)
                                 {
                                    strcpy(linked_remote_system, to_remote_g2[i].to_call);
                                    space_p = strchr(linked_remote_system, ' ');
                                    if (space_p)
                                       *space_p = '\0';
                                    sprintf(notify_msg, "%c_already_linked.dat_LINKED_%s_%c",
                                         to_remote_g2[i].from_mod,
                                         linked_remote_system,
                                         to_remote_g2[i].to_mod);
                                    audio_notify(notify_msg);
                                 }
                              }
                           }
                           else
                           if ((udp_payload[43] == UNLINK_CODE) &&
                               (udp_payload[36] == ' '))
                           {
                              unlink_token = true;

                              /*

                              if (ONLY_LINK_UNLINK)
                                traceit("ONLY_LINK_UNLINK IS TRUE\n");

                              if (!ONLY_LINK_UNLINK)
                               traceit ("ONLY_LINK_UNLINK IS FALSE\n");

                              */

                              if (ONLY_LINK_UNLINK &&
                                  (link_unlink_user.find(call) == link_unlink_user.end()))
                              {
                                 //traceit("unlink request denied A, unauthorized rf user [%s]\n", call);
                                 unlink_token = false;
                              }
                              
                              if (!ONLY_LINK_UNLINK &&
                                  (link_unlink_user.find(call) != link_unlink_user.end()))
                              {
                                 //traceit("unlink request denied X, unauthorized rf user [%s]\n", call);
                                 unlink_token = false;
                              }


                              //else

                              /* VA3UV - v3.12 - added check to make sure MyCALL is valid */

                              if (valid_callsigns.find(call) == valid_callsigns.end())
                              {
                                 traceit("Invalid mycall=[%s] rejecting link / unlink request\n", call);
                                 unlink_token = false;
                              }

                              /*

                              if (ONLY_LINK_UNLINK &&
                                  (link_unlink_user.find(call) == link_unlink_user.end()))
                              {
                                 traceit("unlink request denied B, unauthorized rf user [%s]\n", call);
                              }
                               */
                              

                              else
                              {
                                 if (to_remote_g2[i].to_call[0] != '\0' && unlink_token)
                                 {
                                    traceit("Unlinked from [%s] mod %c\n", 
                                          to_remote_g2[i].to_call, to_remote_g2[i].to_mod);

                                    sprintf(notify_msg, "%c_unlinked.dat_UNLINKED", to_remote_g2[i].from_mod);

                                    // v3.18

                                    sprintf(df_b, "/dstar/tmp/blocklinking-%c", tolower(to_remote_g2[i].from_mod));
                                    unlink(df_b);
                                    if (to_remote_g2[i].type == 'p' && unlink_token)
                                    {
                                       queryCommand[0] = 0x05;
                                       queryCommand[1] = 0x00;
                                       queryCommand[2] = 0x18;
                                       queryCommand[3] = ((to_remote_g2[i].from_mod - 'A') << 4) | (to_remote_g2[i].to_mod - 'A');
                                       queryCommand[4] = 0x00;
                                       for (j = 0; j < 3; j++)
                                          sendto(ref_g2_sock,(char *)queryCommand,5,0,
                                                 (struct sockaddr *)&(to_remote_g2[i].toDst4),
                                                  sizeof(to_remote_g2[i].toDst4));
                                    }
                                    else
                                    if (to_remote_g2[i].type == 'x' && unlink_token)
                                    {
                                       strcpy(unlink_request, OWNER);
                                       unlink_request[8] = to_remote_g2[i].from_mod;
                                       unlink_request[9] = ' ';
                                       unlink_request[10] = '\0';

                                       for (j = 0; j < 5; j++)
                                          sendto(xrf_g2_sock,unlink_request, CALL_SIZE + 3,0,
                                              (struct sockaddr *)&(to_remote_g2[i].toDst4),
                                              sizeof(to_remote_g2[i].toDst4));
                                    }
                                    else
                                    if (to_remote_g2[i].type == 'd' && unlink_token)
                                    {
                                       strcpy(cmd_2_dcs, OWNER);
                                       cmd_2_dcs[8] = to_remote_g2[i].from_mod;
                                       cmd_2_dcs[9] = ' ';
                                       cmd_2_dcs[10] = '\0';
                                       memcpy(cmd_2_dcs + 11, to_remote_g2[i].to_call, 8);

                                       for (j = 0; j < 5; j++)
                                          sendto(dcs_g2_sock, cmd_2_dcs, 19,0,
                                                 (struct sockaddr *)&(to_remote_g2[i].toDst4),
                                                 sizeof(to_remote_g2[i].toDst4));
                                    }

                                    /* now zero out this entry */
                                    to_remote_g2[i].type = ' ';
                                    to_remote_g2[i].to_call[0] = '\0';
                                    memset(&(to_remote_g2[i].toDst4),0,sizeof(struct sockaddr_in));
                                    to_remote_g2[i].from_mod = ' ';
                                    to_remote_g2[i].to_mod = ' ';
                                    to_remote_g2[i].countdown = 0;
                                    to_remote_g2[i].is_connected = false;
                                    to_remote_g2[i].in_streamid[0] = 0x00;
                                    to_remote_g2[i].in_streamid[1] = 0x00;

                                    print_status_file();
                                    audio_notify(notify_msg);
                                 }
                                 else
                                 {
                                    if (unlink_token)
                                    {
                                    sprintf(notify_msg, "%c_already_unlinked.dat_UNLINKED", udp_payload[35]);
                                    audio_notify(notify_msg);
                                    }
                                 }
                              }
                           }
                           else

                           /* VA3UV - v3.12 - added check to make sure MyCALL is valid */

                           if ((valid_callsigns.find(call) != valid_callsigns.end()) && (udp_payload[43] == INFO_CODE) &&
                               (udp_payload[36] == ' '))
                           {
                              if (to_remote_g2[i].is_connected)
                              {
                                 strcpy(linked_remote_system, to_remote_g2[i].to_call);
                                 space_p = strchr(linked_remote_system, ' ');
                                 if (space_p)
                                    *space_p = '\0';
                                 sprintf(notify_msg, "%c_linked.dat_LINKED_%s_%c",
                                         to_remote_g2[i].from_mod,
                                         linked_remote_system,
                                         to_remote_g2[i].to_mod);
                                 audio_notify(notify_msg);
                              }
                              else
                              {
                                 sprintf(notify_msg, "%c_id.dat_%s_NOT_LINKED", udp_payload[35], OWNER);
                                 audio_notify(notify_msg);
                              }
                           }
                           else
                           /*  v3.18 remove the exec code functionality

                           if ((udp_payload[43] == EXEC_CODE) &&
                               (udp_payload[36] == ' ') &&
                               (admin.find(call) != admin.end())) // only ADMIN can execute scripts
                           {
                              if (udp_payload[42] != ' ')
                              {
                                 memset(system_cmd, '\0', sizeof(system_cmd));
                                 snprintf(system_cmd, FILENAME_MAX, "%s/exec_%c.sh %s %c &", 
                                          ANNOUNCE_DIR, 
                                          udp_payload[42], call, udp_payload[35]);
                                 traceit("Executing %s\n", system_cmd);
                                 system(system_cmd);
                              }
                           }
                           
                           */

                           // v3.15 - allow ADMIN users to disable the RF_INACTIVITY_TIMER
                                   
                          if ((udp_payload[43] == RESET_TIMER_CODE) &&
                             (admin.find(call) != admin.end()))
                          {

                          if (udp_payload[35] == 'A')       
                          {         
                            // traceit("Point B\n");
                            RF_INACTIVITY_TIMER[0] = 0;
                            traceit("RF INACTIVITY TIMER - MODULE A DISABLED\n");
                            sprintf(notify_msg, "%c_timer_disabled.dat_%s_TIMER_DIS", udp_payload[35], OWNER);       
                            audio_notify(notify_msg);

                          }


                          if (udp_payload[35] == 'B')
                          {
                            // traceit("Point B\n");
                            RF_INACTIVITY_TIMER[1] = 0;
                            traceit("RF INACTIVITY TIMER - MODULE B DISABLED\n");
                            sprintf(notify_msg, "%c_timer_disabled.dat_%s_TIMER_DIS", udp_payload[35], OWNER);
                            audio_notify(notify_msg);

                          }


                          if (udp_payload[35] == 'C')
                          {
                            // traceit("Point B\n");
                            RF_INACTIVITY_TIMER[2] = 0;
                            traceit("RF INACTIVITY TIMER - MODULE C DISABLED\n");

                            sprintf(notify_msg, "%c_timer_disabled.dat_%s_TIMER_DIS", udp_payload[35], OWNER);       
                            audio_notify(notify_msg);

                          }

                     }
                  
                     if ((udp_payload[43] == RESTORE_TIMER_CODE) &&             
                     (admin.find(call) != admin.end()))

                     {
                     if (udp_payload[35] == 'A')       
                     {
                      
                     RF_INACTIVITY_TIMER[0] = RF_INACTIVITY_TIMER_SAVE[0];
                     traceit("RF INACTIVITY TIMER - MODULE A RESTORED\n");
                     sprintf(notify_msg, "%c_timer_enabled.dat_%s_TIMER_ENA", udp_payload[35], OWNER);       
                        audio_notify(notify_msg);

                     }

                     if (udp_payload[35] == 'B')       
                     {
                                                 
                     RF_INACTIVITY_TIMER[1] = RF_INACTIVITY_TIMER_SAVE[1];
                     traceit("RF INACTIVITY TIMER - MODULE B RESTORED\n");
                     sprintf(notify_msg, "%c_timer_enabled.dat_%s_TIMER_ENA", udp_payload[35], OWNER);        
                        audio_notify(notify_msg);
                     }

                     if (udp_payload[35] == 'C')        
                     {

                     RF_INACTIVITY_TIMER[2] = RF_INACTIVITY_TIMER_SAVE[2];
                     traceit("RF INACTIVITY TIMER - MODULE C RESTORED\n");

                     sprintf(notify_msg, "%c_timer_enabled.dat_%s_TIMER_ENA", udp_payload[35], OWNER);        
                        audio_notify(notify_msg);
                     }
                   }

                   else
                           if ((udp_payload[42] == DONGLE_CODE) &&
                               (udp_payload[36] == ' ') &&
                               (admin.find(call) != admin.end())) // only ADMIN can block dongle users
                           {
                              if (udp_payload[43] == '1')
                              {
                                 MAX_DONGLES = SAVED_MAX_DONGLES;
                                 traceit("Dongle connections are now allowed\n");
                              }
                              else
                              if (udp_payload[43] == '0')
                              {
                                 inbound_list.clear();
                                 MAX_DONGLES = 0;
                                 traceit("Dongle connections are now disallowed\n");
                              }
                           }
                           else
                           if ((udp_payload[43] == FILE_REFRESH_GWYS_CODE) &&
                               (udp_payload[36] == ' ') &&
                               (admin.find(call) != admin.end())) // only ADMIN can reload gwys.txt
                           {
                              load_gwys(GWYS);
                              load_valid_callsigns(VALID_CALLSIGNS);
                           }
                           // v3.18 else

                           /* v3.18 if ((valid_callsigns.find(call) != valid_callsigns.end()) && (udp_payload[43] == ECHO_CODE) &&
                               (udp_payload[36] == ' '))

                           //if ((udp_payload[43] == ECHO_CODE) &&
                               (udp_payload[36] == ' '))
                           {
                              if (recd[i].fd >= 0)
                                 traceit("Already recording for echotest on mod %d\n", i);
                              else
                              {
                                 memset(tempfile, '\0', sizeof(tempfile));
                                 snprintf(tempfile, FILENAME_MAX, "%s/%c_%s",
                                          ECHOTEST_DIR,
                                          udp_payload[35], "echotest.dat");

                                 recd[i].fd = open(tempfile,
                                               O_CREAT | O_WRONLY | O_EXCL | O_TRUNC | O_APPEND,
                                               S_IRUSR | S_IWUSR | S_IRGRP | S_IROTH);
                                 if (recd[i].fd < 0)
                                    traceit("Failed to create file %s for echotest\n", tempfile);
                                 else
                                 {
                                    strcpy(recd[i].file, tempfile);  
                                    traceit("Recording mod %c for echotest into file:[%s]\n",
                                            udp_payload[35],
                                            recd[i].file);

                                    time(&recd[i].last_time);
                                    memcpy(recd[i].streamid, udp_payload + 14, 2);
                                    
                                    memcpy(recbuf, "DSVT", 4);
                                    recbuf[4] = 0x10;
                                    recbuf[5] = 0x00;
                                    recbuf[6] = 0x00;
                                    recbuf[7] = 0x00;
                                    recbuf[8] =  udp_payload[10];
                                    recbuf[9] =  udp_payload[11];
                                    recbuf[10] = udp_payload[12];
                                    recbuf[11] = udp_payload[13];
                                    memcpy(recbuf + 12, udp_payload + 14, 44);

                                    recbuf[15] = 0x00;

                                    memset(recbuf + 18, ' ', CALL_SIZE);
                                    memcpy(recbuf + 18, OWNER, strlen(OWNER));
                                    recbuf[25] = udp_payload[35];
                                    memset(recbuf + 26, ' ', CALL_SIZE);
                                    memcpy(recbuf + 26,  OWNER, strlen(OWNER));
                                    recbuf[33] = 'G';
                                    memcpy(recbuf + 34, "CQCQCQ  ", 8);

                                    calcPFCS(recbuf,56);

                                    rec_len = 56;
                                    (void)write(recd[i].fd, "DVTOOL", 6);
                                    (void)write(recd[i].fd, &num_recs, 4);
                                    (void)write(recd[i].fd, &rec_len, 2);
                                    (void)write(recd[i].fd, (char *)recbuf, rec_len);
                                 }
                              }
                           } */
                        }

                        /* send data to the donglers */
                        /* good band, normal packet */
                        if ((inbound_list.size() > 0) && (i >= 0) &&
                            ((udp_payload[17] == 0x00) ||
                             (udp_payload[17] == 0x08) ||
                             (udp_payload[17] == 0x20) ||
                             (udp_payload[17] == 0x28)))
                        {
                           readBuffer2[0] = (unsigned char)(58 & 0xFF);
                           readBuffer2[1] = (unsigned char)(58 >> 8 & 0x1F);
                           readBuffer2[1] = (unsigned char)(readBuffer2[1] | 0xFFFFFF80);

                           memcpy(readBuffer2 + 2, "DSVT", 4);
                           readBuffer2[6] = 0x10;
                           readBuffer2[7] = 0x00;
                           readBuffer2[8] = 0x00;
                           readBuffer2[9] = 0x00;
                           readBuffer2[10] = udp_payload[10];
                           readBuffer2[11] = udp_payload[11];
                           readBuffer2[12] = udp_payload[12];
                           readBuffer2[13] = udp_payload[13];
                           memcpy(readBuffer2 + 14, udp_payload + 14, 44);
                           memcpy(readBuffer2 + 20, OWNER, CALL_SIZE);
                           readBuffer2[27] = udp_payload[35];
                           memcpy(readBuffer2 + 28, OWNER, CALL_SIZE);
                           readBuffer2[35] = 'G';
                           memcpy(&readBuffer2[36], "CQCQCQ  ", 8);

                           /* save the header for re-transmit to plus dongles later */
                           if (udp_payload[35] == 'A')
                           {
                              memcpy(regen_hdr_for_plus_dongles[0].buf, readBuffer2, 58);
                              regen_hdr_for_plus_dongles[0].streamid[0] = udp_payload[14];
                              regen_hdr_for_plus_dongles[0].streamid[1] = udp_payload[15];
                           }
                           else
                           if (udp_payload[35] == 'B')
                           {
                              memcpy(regen_hdr_for_plus_dongles[1].buf, readBuffer2, 58);
                              regen_hdr_for_plus_dongles[1].streamid[0] = udp_payload[14];
                              regen_hdr_for_plus_dongles[1].streamid[1] = udp_payload[15];
                           }
                           else
                           if (udp_payload[35] == 'C')
                           {
                              memcpy(regen_hdr_for_plus_dongles[2].buf, readBuffer2, 58);
                              regen_hdr_for_plus_dongles[2].streamid[0] = udp_payload[14];
                              regen_hdr_for_plus_dongles[2].streamid[1] = udp_payload[15];
                           }

                           for (pos = inbound_list.begin(); pos != inbound_list.end(); pos++)
                           {
                              inbound_ptr = (inbound *)pos->second;
                              for (j = 0; j < 5; j++)
                                 sendto(ref_g2_sock, (char *)readBuffer2, 58,
                                        0,(struct sockaddr *)&(inbound_ptr->sin),
                                        sizeof(struct sockaddr_in));
                           }
                        }

                        /* good band, normal packet */
                        if ((i >= 0) &&
                            ((udp_payload[17] == 0x00) ||
                             (udp_payload[17] == 0x08) ||
                             (udp_payload[17] == 0x20) ||
                             (udp_payload[17] == 0x28)))
                        {
                           /* do we have to multilink? */
                           /* make sure the source is linked to a plus ref */
                           if ((to_remote_g2[i].is_connected) &&

                               (
                                 ((memcmp(to_remote_g2[i].to_call, "REF", 3) == 0) && (to_remote_g2[i].type == 'p'))
                                          ||
                                 ((memcmp(to_remote_g2[i].to_call, "XRF", 3) == 0) && (to_remote_g2[i].type == 'x'))
                               ) &&

                               /* only CQCQCQ */
                               (memcmp(udp_payload + 20, OWNER, 7) == 0) &&
                               (memcmp(udp_payload + 36, "CQCQCQ", 6) == 0) &&
                               (udp_payload[27] == 'G'))
                           {
                              ml_from_rptr_idx = 0;
                              streamid_raw = (udp_payload[14] * 256U) + udp_payload[15];

                              for (j = 0; j < 3; j++)
                              {
                                 if ((j != i) &&
                                     (to_remote_g2[j].is_connected) &&
                                     (memcmp(to_remote_g2[j].to_call, to_remote_g2[i].to_call, 8) == 0) &&
                                     (to_remote_g2[j].to_mod == to_remote_g2[i].to_mod) &&
                                     (to_remote_g2[j].to_mod != 'E'))
                                 {
                                    memcpy(multilink + 2, "DSVT", 4);
                                    multilink[6] = 0x10;
                                    multilink[7] = 0x00;
                                    multilink[8] = 0x00;
                                    multilink[9] = 0x00;
                                    multilink[10] = udp_payload[10];
                                    multilink[11] = udp_payload[11];
                                    multilink[12] = udp_payload[12];
                                    multilink[13] = udp_payload[13]; 
                                    memcpy(multilink + 14, udp_payload + 14, 44);

                                    streamid_raw ++;
                                    if (streamid_raw == 0)
                                       streamid_raw ++;
                                    multilink[14] = streamid_raw / 256U;
                                    multilink[15] = streamid_raw % 256U;

                                    memcpy(multilink + 20, OWNER, 8);
                                    multilink[27] = to_remote_g2[j].from_mod;
                                    memcpy(multilink + 28, OWNER, 8);
                                    multilink[35] = 'G';

                                    memcpy(&multilink[36], "CQCQCQ  ", 8);
           
                                    calcPFCS(multilink + 2, 56);
                                  
                                    sendto(ref_g2_sock, (char *)multilink + 2,56,0,(struct sockaddr *)&toLocalg2,sizeof(struct sockaddr_in));

                                    ml_from_rptr.from_rptr_streamid[0] = udp_payload[14];
                                    ml_from_rptr.from_rptr_streamid[1] = udp_payload[15];
                                    ml_from_rptr.to_rptr_streamid[ml_from_rptr_idx][0] = multilink[14];
                                    ml_from_rptr.to_rptr_streamid[ml_from_rptr_idx][1] = multilink[15];
                                    ml_from_rptr_idx ++;
                                 }
                              }
                           }

                           if (to_remote_g2[i].is_connected) 
                           {
                              if ((memcmp(udp_payload + 20, OWNER, 7) == 0) && 
                                  (memcmp(udp_payload + 36, "CQCQCQ", 6) == 0) &&
                                  (udp_payload[27] == 'G'))                  
                              {
                                 if ((to_remote_g2[i].type == 'x') || (to_remote_g2[i].type == 'p'))
                                 {
                                    readBuffer2[0] = (unsigned char)(58 & 0xFF);
                                    readBuffer2[1] = (unsigned char)(58 >> 8 & 0x1F);
                                    readBuffer2[1] = (unsigned char)(readBuffer2[1] | 0xFFFFFF80);

                                    memcpy(readBuffer2 + 2, "DSVT", 4);
                                    readBuffer2[6] = 0x10;
                                    readBuffer2[7] = 0x00;
                                    readBuffer2[8] = 0x00;
                                    readBuffer2[9] = 0x00;
                                    readBuffer2[10] = udp_payload[10];

                                    memcpy(readBuffer2 + 14, udp_payload + 14, 44);

                                    memcpy(&readBuffer2[36], "CQCQCQ  ", 8);

                                    if (to_remote_g2[i].type == 'x')
                                    {
                                       to_remote_g2[i].out_streamid[0] = udp_payload[14];
                                       to_remote_g2[i].out_streamid[1] = udp_payload[15];

                                       readBuffer2[11] = udp_payload[11];
                                       readBuffer2[12] = udp_payload[12];
                                       /*** readBuffer2[13] = udp_payload[13]; ***/
                        
                                       /* inform XRF about the source */
                                       readBuffer2[13] = to_remote_g2[i].from_mod;

                                       memset(readBuffer2 + 20, ' ', CALL_SIZE);
                                       memcpy(readBuffer2 + 20, to_remote_g2[i].to_call,
                                                  strlen(to_remote_g2[i].to_call));
                                       readBuffer2[27] = to_remote_g2[i].to_mod;
                                       memset(readBuffer2 + 28, ' ', CALL_SIZE);
                                       memcpy(readBuffer2 + 28, to_remote_g2[i].to_call,
                                                     strlen(to_remote_g2[i].to_call));
                                       readBuffer2[35] = 'G';

                                       calcPFCS(readBuffer2 + 2,56);

                                       for (j = 0; j < 5; j++)
                                          sendto(xrf_g2_sock, (char *)readBuffer2 + 2, 56,
                                              0,(struct sockaddr *)&(to_remote_g2[i].toDst4),
                                              sizeof(struct sockaddr_in));
                                    } 
                                    else
                                    {
                                       if (valid_callsigns.find(call) == valid_callsigns.end())
                                          traceit("Unauthorized callsign [%s]\n", call); 
                                       else
                                       {
                                          to_remote_g2[i].out_streamid[0] = udp_payload[14];
                                          to_remote_g2[i].out_streamid[1] = udp_payload[15];

                                          if (to_remote_g2[i].from_mod == 'A')
                                             readBuffer2[11] = 0x41;
                                          else
                                          if (to_remote_g2[i].from_mod == 'B')
                                             readBuffer2[11] = 0x42;
                                          else
                                          if (to_remote_g2[i].from_mod == 'C')
                                             readBuffer2[11] = 0x43;

                                          readBuffer2[12] = 0xa5;
                                          readBuffer2[13] = readBuffer2[11];

                                          calcPFCS(readBuffer2 + 2,56);

                                          /* save the header for re-transmit to plus ref later */
                                          memcpy(regen_hdr_for_plus_refs[i].buf, readBuffer2, 58);

                                          for (j = 0; j < 5; j++)
                                            sendto(ref_g2_sock, (char *)readBuffer2, 58,
                                                0,(struct sockaddr *)&(to_remote_g2[i].toDst4),
                                                sizeof(struct sockaddr_in));
                                       }
                                    }
                                 }
                                 else
                                 if (to_remote_g2[i].type == 'd')
                                 {
                                    to_remote_g2[i].out_streamid[0] = udp_payload[14];
                                    to_remote_g2[i].out_streamid[1] = udp_payload[15];

                                    memcpy(rptr_2_dcs[i].mycall, udp_payload + 44, 8);
                                    memcpy(rptr_2_dcs[i].sfx, udp_payload + 52, 4);
                                    rptr_2_dcs[i].dcs_rptr_seq = 0;
                                 }
                              }
                           }
                        }
                     }
                     else
                     {
                        /* process dtmf tones */
                        for (i = 0; i < 3; i++)
                        {
                           if (memcmp(tracing[i].streamid, udp_payload + 14, 2) == 0)
                           {
                              if ((udp_payload[16] & 0x40) != 0)
                              {
                                 if (RPTR_ACK)
                                    rptr_ack(i);

                                 /* dtmf stuff */
                                 if (dtmf_buf_count[i] > 0)
                                 {
                                    memset(DTMF_FILE, 0, sizeof(DTMF_FILE));
                                    snprintf(DTMF_FILE, FILENAME_MAX, "%s/%d_mod_DTMF_NOTIFY", DTMF_DIR, i);
                                    traceit("Saving dtmfs=[%s] into file: [%s]\n", dtmf_buf[i], DTMF_FILE);
                                    dtmf_fp = fopen(DTMF_FILE, "w");
                                    if (!dtmf_fp)
                                       traceit("Failed to create dtmf file %s\n", DTMF_FILE);
                                    else
                                    {
                                       fprintf(dtmf_fp, "%s\n%s", dtmf_buf[i], dtmf_mycall[i]);
                                       fclose(dtmf_fp); dtmf_fp = NULL;
                                    }
                                    memset(dtmf_buf[i], 0, sizeof(dtmf_buf[i]));
                                    dtmf_buf_count[i] = 0;
                                    dtmf_counter[i] = 0;
                                    dtmf_last_frame[i] = 0;
                                 }

                                 memset(dtmf_mycall[i], 0, sizeof(dtmf_mycall[i]));

                                 new_group[i] = true;
                                 GPS_seen[i] = false;

                                 tracing[i].streamid[0] = 0x00;
                                 tracing[i].streamid[1] = 0x00;
                              }
                              else
                              {

                                 if (!GPS_seen[i])
                                 {
                                    if (udp_payload_len == 29)
                                       memcpy(tmp_txt, udp_payload + 26, 3);
                                    else
                                       memcpy(tmp_txt, udp_payload + 29, 3);

                                    if ((tmp_txt[0] != 0x55) || (tmp_txt[1] != 0x2d) || (tmp_txt[2] != 0x16))
                                    {
                                       if (new_group[i])
                                       {
                                          tmp_txt[0] = tmp_txt[0] ^ 0x70;
                                          header_type = tmp_txt[0] & 0xf0;

                                          if ((header_type == 0x50) ||  /* header  */
                                              (header_type == 0xc0))    /* squelch */
                                             new_group[i] = false;
                                          else
                                          if (header_type == 0x30)  /* GPS or GPS id or APRS */
                                          {
                                             GPS_seen[i] = true;
                                             new_group[i] = false;

                                             memcpy(tmp1, dtmf_mycall[i], 8); tmp1[8] = '\0';

                                             // delete the user if exists and it is a local RF entry
                                             p_tmp2 = NULL;
                                             for (dt_lh_pos = dt_lh_list.begin(); dt_lh_pos != dt_lh_list.end();  dt_lh_pos++)
                                             {
                                                if (strcmp((char *)dt_lh_pos->second.c_str(), tmp1) == 0)
                                                {
                                                   strcpy(tmp2, (char *)dt_lh_pos->first.c_str());
                                                   p_tmp2 = strstr(tmp2, "=l");
                                                   if (p_tmp2)
                                                   {
                                                      dt_lh_list.erase(dt_lh_pos);
                                                      break;
                                                   }
                                                }
                                             }
                                             /* we have tmp1 and tmp2, we have the user and it is already been removed */
                                             /* add the user with gps indicator g */
                                             if (p_tmp2)
                                             {
                                                *(p_tmp2 + 1) = 'g';
                                                dt_lh_list[tmp2] = tmp1;
                                             }
                                          }
                                          else
                                          if (header_type == 0x40) /* ABC text */
                                             new_group[i] = false;
                                          else
                                             new_group[i] = false;
                                       }
                                       else
                                          new_group[i] = true;
                                    }
                                 }

                                 if (udp_payload_len == 29)
                                    ber_errs = dstar_dv_decode(udp_payload + 17, ber_data);
                                 else
                                    ber_errs = dstar_dv_decode(udp_payload + 20, ber_data);

                                 if ((ber_data[0] & 0x0ffc) == 0xfc0)
                                 {
                                    dtmf_digit = (ber_data[0] & 0x03) | ((ber_data[2] & 0x60) >> 3);
                                    if (dtmf_counter[i] > 0)
                                    {
                                       if (dtmf_last_frame[i] != dtmf_digit)
                                       dtmf_counter[i] = 0;
                                    }
                                    dtmf_last_frame[i] = dtmf_digit;
                                    dtmf_counter[i] ++;

                                    if ((dtmf_counter[i] == 5) && (dtmf_digit >= 0) && (dtmf_digit <= 15))
                                    {
                                       if (dtmf_buf_count[i] < MAX_DTMF_BUF)
                                       {
                                          dtmf_buf[i][ dtmf_buf_count[i] ] = dtmf_chars[dtmf_digit];
                                          dtmf_buf_count[i] ++;
                                       }
                                    }
                                    if (udp_payload_len == 29)
                                       memcpy(udp_payload + 17, silence, 9);
                                    else
                                       memcpy(udp_payload + 20, silence, 9);
                                 }
                                 else
                                    dtmf_counter[i] = 0;
                              }
                              break;
                           }
                        }

                        if (inbound_list.size() > 0)
                        {
                           readBuffer2[0] = (unsigned char)(29 & 0xFF);
                           readBuffer2[1] = (unsigned char)(29 >> 8 & 0x1F);
                           readBuffer2[1] = (unsigned char)(readBuffer2[1] | 0xFFFFFF80);

                           memcpy(readBuffer2 + 2, "DSVT", 4);
                           readBuffer2[6] = 0x20;
                           readBuffer2[7] = 0x00;
                           readBuffer2[8] = 0x00;
                           readBuffer2[9] = 0x00;
                           readBuffer2[10] = udp_payload[10];
                           readBuffer2[11] = udp_payload[11];
                           readBuffer2[12] = udp_payload[12];
                           readBuffer2[13] = udp_payload[13];
                           memcpy(readBuffer2 + 14, udp_payload + 14, 3);
                           if (udp_payload_len == 29)
                              memcpy(readBuffer2 + 17, udp_payload + 17, 12);
                           else
                              memcpy(readBuffer2 + 17, udp_payload + 20, 12);

                           for (pos = inbound_list.begin(); pos != inbound_list.end(); pos++)
                           {
                              inbound_ptr = (inbound *)pos->second;

                              /* re-transmit header on SYNC */
                              if ((readBuffer2[26] == 0x55) && (readBuffer2[27] == 0x2d) && (readBuffer2[28] == 0x16))
                              {
                                 for (i = 0; i < 3; i++)
                                 {
                                    if ((regen_hdr_for_plus_dongles[i].streamid[0] == udp_payload[14]) &&
                                        (regen_hdr_for_plus_dongles[i].streamid[1] == udp_payload[15]))
                                    {
                                       sendto(ref_g2_sock, (char *)regen_hdr_for_plus_dongles[i].buf, 58, 0,
                                              (struct sockaddr *)&(inbound_ptr->sin),
                                              sizeof(struct sockaddr_in));
                                       break;
                                    }
                                 }
                              }

                              sendto(ref_g2_sock, (char *)readBuffer2, 29, 0,
                                     (struct sockaddr *)&(inbound_ptr->sin),
                                     sizeof(struct sockaddr_in));
                           }
                           if ((udp_payload[16] & 0x40) != 0)
                           {
                              for (i = 0; i < 3; i++)
                              {
                                 if ((regen_hdr_for_plus_dongles[i].streamid[0] == udp_payload[14]) &&
                                     (regen_hdr_for_plus_dongles[i].streamid[1] == udp_payload[15]))
                                 {
                                    regen_hdr_for_plus_dongles[i].streamid[0] = 0x00;
                                    regen_hdr_for_plus_dongles[i].streamid[1] = 0x00;
                                    break;
                                 }
                              }
                           }
                        }

                        for (i = 0; i < 3; i++)
                        {
                           /* v3.18 if ((recd[i].fd >= 0) &&
                               (memcmp(recd[i].streamid, udp_payload + 14, 2) == 0))
                           {
                              time(&recd[i].last_time);
            
                              memcpy(recbuf, "DSVT", 4);
                              recbuf[4] = 0x20;
                              recbuf[5] = 0x00;
                              recbuf[6] = 0x00;
                              recbuf[7] = 0x00;
                              recbuf[8] = udp_payload[10];
                              recbuf[9] = udp_payload[11];
                              recbuf[10] = udp_payload[12];
                              recbuf[11] = udp_payload[13];
                              memcpy(recbuf + 12, udp_payload + 14, 3);
                              if (udp_payload_len == 29)
                                 memcpy(recbuf + 15, udp_payload + 17, 12);
                              else
                                 memcpy(recbuf + 15, udp_payload + 20, 12);

                              rec_len = 27;
                              (void)write(recd[i].fd, &rec_len, 2);
                              (void)write(recd[i].fd, (char *)recbuf, rec_len);

                              if ((udp_payload[16] & 0x40) != 0)
                              {
                                 recd[i].streamid[0] = 0x00; 
                                 recd[i].streamid[1] = 0x00;
                                 recd[i].last_time = 0;
                                 close(recd[i].fd); recd[i].fd = -1;
                                 // traceit("Closed echotest audio file:[%s]\n", recd[i].file);
        
                                 // we are in echotest mode, so play it back
                                 pthread_attr_init(&echo_attr);
                                 pthread_attr_setdetachstate(&echo_attr, PTHREAD_CREATE_DETACHED);
                                 rc = pthread_create(&echo_thread, &echo_attr, echotest, (void *)recd[i].file);
                                 if (rc != 0)
                                 {
                                    traceit("failed to start echotest thread\n");
                                    
                                    //   When the echotest thread runs, it deletes the file,
                                    //   Because the echotest thread did NOT start, we delete the file here
                                    
                                    unlink(recd[i].file);
                                 }
                                 pthread_attr_destroy(&echo_attr);
                              }
                              break;
                           } */

                           //else
                           if ((to_remote_g2[i].is_connected) &&
                               (memcmp(to_remote_g2[i].out_streamid, udp_payload + 14, 2) == 0))
                           {
                              /* check for multilink */
                              if (memcmp(ml_from_rptr.from_rptr_streamid, udp_payload + 14, 2) == 0)
                              {
                                 memcpy(multilink + 2, "DSVT", 4);
                                 multilink[6] = 0x20;
                                 multilink[7] = 0x00;
                                 multilink[8] = 0x00;
                                 multilink[9] = 0x00;
                                 multilink[10] = udp_payload[10];
                                 multilink[11] = udp_payload[11];
                                 multilink[12] = udp_payload[12];
                                 multilink[13] = udp_payload[13];

                                 memcpy(multilink + 14, udp_payload + 14, 3);

                                 if (udp_payload_len == 29)
                                    memcpy(multilink + 17, udp_payload + 17, 12);
                                 else
                                    memcpy(multilink + 17, udp_payload + 20, 12);

                                 if ((ml_from_rptr.to_rptr_streamid[0][0] != 0x00) ||
                                     (ml_from_rptr.to_rptr_streamid[0][1] != 0x00))
                                 {
                                    multilink[14] = ml_from_rptr.to_rptr_streamid[0][0];
                                    multilink[15] = ml_from_rptr.to_rptr_streamid[0][1];
                                    sendto(ref_g2_sock, (char *)multilink + 2,27,0,(struct sockaddr *)&toLocalg2,sizeof(struct sockaddr_in));
                                 }

                                 if ((ml_from_rptr.to_rptr_streamid[1][0] != 0x00) ||
                                     (ml_from_rptr.to_rptr_streamid[1][1] != 0x00))
                                 {
                                    multilink[14] = ml_from_rptr.to_rptr_streamid[1][0];
                                    multilink[15] = ml_from_rptr.to_rptr_streamid[1][1];
                                    sendto(ref_g2_sock, (char *)multilink + 2,27,0,(struct sockaddr *)&toLocalg2,sizeof(struct sockaddr_in));
                                 }

                                 if ((udp_payload[16] & 0x40) != 0)
                                 {
                                    ml_from_rptr.from_rptr_streamid[0] = ml_from_rptr.from_rptr_streamid[1] = 0x00;
                                    ml_from_rptr.to_rptr_streamid[0][0] = ml_from_rptr.to_rptr_streamid[0][1] = 0x00;
                                    ml_from_rptr.to_rptr_streamid[1][0] = ml_from_rptr.to_rptr_streamid[1][1] = 0x00;
                                    ml_from_rptr_idx = 0;
                                 }
                              }

                              if ((to_remote_g2[i].type == 'x') || (to_remote_g2[i].type == 'p'))
                              {
                                 readBuffer2[0] = (unsigned char)(29 & 0xFF);
                                 readBuffer2[1] = (unsigned char)(29 >> 8 & 0x1F);
                                 readBuffer2[1] = (unsigned char)(readBuffer2[1] | 0xFFFFFF80);

                                 memcpy(readBuffer2 + 2, "DSVT", 4);
                                 readBuffer2[6] = 0x20;
                                 readBuffer2[7] = 0x00;
                                 readBuffer2[8] = 0x00;
                                 readBuffer2[9] = 0x00;
                                 readBuffer2[10] = udp_payload[10];
                                 memcpy(readBuffer2 + 14, udp_payload + 14, 3);
                                 if (udp_payload_len == 29)
                                    memcpy(readBuffer2 + 17, udp_payload + 17, 12);
                                 else
                                    memcpy(readBuffer2 + 17, udp_payload + 20, 12);

                                 if (to_remote_g2[i].type == 'x')
                                 {
                                    readBuffer2[11] = udp_payload[11];
                                    readBuffer2[12] = udp_payload[12];
                                    /*** readBuffer2[13] = udp_payload[13]; ***/

                                    /* inform XRF about the source */
                                    readBuffer2[13] = to_remote_g2[i].from_mod;

                                    sendto(xrf_g2_sock, (char *)readBuffer2 + 2, 27,
                                        0,(struct sockaddr *)&(to_remote_g2[i].toDst4),
                                        sizeof(struct sockaddr_in));
                                 }
                                 else
                                 {
                                    if (to_remote_g2[i].from_mod == 'A')
                                       readBuffer2[11] = 0x41;
                                    else
                                    if (to_remote_g2[i].from_mod == 'B')
                                       readBuffer2[11] = 0x42;
                                    else
                                    if (to_remote_g2[i].from_mod == 'C')
                                       readBuffer2[11] = 0x43;

                                    readBuffer2[12] = 0xa5;
                                    readBuffer2[13] = readBuffer2[11];

                                    /* re-transmit header on SYNC */
                                    if ((readBuffer2[26] == 0x55) && (readBuffer2[27] == 0x2d) && (readBuffer2[28] == 0x16))
                                       sendto(ref_g2_sock, (char *)regen_hdr_for_plus_refs[i].buf, 58,
                                              0,(struct sockaddr *)&(to_remote_g2[i].toDst4),
                                              sizeof(struct sockaddr_in));

                                    sendto(ref_g2_sock, (char *)readBuffer2, 29,
                                           0,(struct sockaddr *)&(to_remote_g2[i].toDst4),
                                           sizeof(struct sockaddr_in));
                                 }
                              }
                              else
                              if (to_remote_g2[i].type == 'd')
                              {
                                 memset(dcs_buf, 0x00, 600);
                                 dcs_buf[0] = dcs_buf[1] = dcs_buf[2] = '0';
                                 dcs_buf[3] = '1';
                                 dcs_buf[4] = dcs_buf[5] = dcs_buf[6] = 0x00;
                                 memcpy(dcs_buf + 7, to_remote_g2[i].to_call, 8);
                                 dcs_buf[14] = to_remote_g2[i].to_mod;
                                 memcpy(dcs_buf + 15, OWNER, 8);
                                 dcs_buf[22] = to_remote_g2[i].from_mod;
                                 memcpy(dcs_buf + 23, "CQCQCQ  ", 8);
                                 memcpy(dcs_buf + 31, rptr_2_dcs[i].mycall, 8);
                                 memcpy(dcs_buf + 39, rptr_2_dcs[i].sfx, 4);
                                 dcs_buf[43] = udp_payload[14];  /* streamid0 */
                                 dcs_buf[44] = udp_payload[15];  /* streamid1 */
                                 dcs_buf[45] = udp_payload[16];  /* cycle sequence */
                                 if (udp_payload_len == 29) 
                                    memcpy(dcs_buf + 46, udp_payload + 17, 12);
                                 else
                                    memcpy(dcs_buf + 46, udp_payload + 20, 12);

                                 dcs_buf[58] = (rptr_2_dcs[i].dcs_rptr_seq >> 0)  & 0xff;
                                 dcs_buf[59] = (rptr_2_dcs[i].dcs_rptr_seq >> 8)  & 0xff;
                                 dcs_buf[60] = (rptr_2_dcs[i].dcs_rptr_seq >> 16) & 0xff;

                                 rptr_2_dcs[i].dcs_rptr_seq ++;

                                 dcs_buf[61] = 0x01;
                                 dcs_buf[62] = 0x00;

                                 sendto(dcs_g2_sock, dcs_buf, 100, 0,
                                           (struct sockaddr *)&(to_remote_g2[i].toDst4),
                                           sizeof(to_remote_g2[i].toDst4));
                              }

                              if ((udp_payload[16] & 0x40) != 0)
                              {
                                 to_remote_g2[i].out_streamid[0] = 0x00;
                                 to_remote_g2[i].out_streamid[1] = 0x00;
                              }
                              break;
                           }
                        } 

                        if ((udp_payload[16] & 0x40) != 0)
                        {
                        /* update the last time we heard an RF user */
                        tracing[i].last_time = time(NULL);
                        //traceit("RF activity reset timer\n");

                        // Here we create a file "local_rf_use_A|B|C with a timestamp of the last time that an RF user was heard
                        // This can then be used by an external script to sense whether the repeater is in use, for re-linking to a default reflector, etc
                        //
                        //traceit("udp_payload_35 = %c\n", udp_payload[35]);

                        uv_mod[0]=uv_rf_module;
                        uv_mod[1]='\0';

                        strcpy(rf_file, RF_FLAGS_DIR);
                        strcat(rf_file, "/");
                        strcat(rf_file, "local_rf_use_");
                        strcat(rf_file, uv_mod);
                        strcat(rf_file, ".txt"); 

                        FILE *fp;
                        fp = fopen (rf_file, "w");
                        fclose(fp);

                           if (QSO_DETAILS)
                              traceit("END from rptr: cntr=%02x %02x, streamID=%d,%d, %d bytes\n",
                                      udp_payload[4], udp_payload[5],
                                      udp_payload[14],udp_payload[15],udp_payload_len);
                        }
                     }
                  }
               }
            }
         }
         FD_CLR (rptr_sock,&fdset);
      }
   }
}

void audio_notify(char *msg)
{
   if (!ANNOUNCE)
      return;

   short int i = 0;
   static char notify_msg[3][64];

   if (*msg == 'A')
      i = 0;
   else
   if (*msg == 'B')
      i = 1;
   else
   if (*msg == 'C')
      i = 2;

   strcpy(notify_msg[i], msg);

   int rc = 0;
   pthread_t audio_notify_thread;
   pthread_attr_t attr;

   pthread_attr_init(&attr);
   pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED);
   rc = pthread_create(&audio_notify_thread, &attr, audio_notify_run, (void *)(notify_msg[i]));
   if (rc != 0)
      traceit("failed to start audio_notify thread for mod %c\n", *msg);
   pthread_attr_destroy(&attr);
   return;
}

static void *audio_notify_run(void *arg)
{
   char notify_msg[64];

   strcpy(notify_msg, (char *)arg);

   unsigned short rlen = 0;
   size_t nread = 0;
   unsigned char dstar_buf[56];
   bool useTEXT = false;
   short int TEXT_idx = 0;
   char RADIO_ID[21];
   char temp_file[FILENAME_MAX + 1];
   FILE *fp = NULL;
   char mod;
   char *p = NULL;
   u_int16_t streamid_raw = 0;
   struct timespec nanos;
   unsigned int aseed;
   time_t tnow = 0;
   struct sigaction act;

   /* example: A_linked.dat_LINKED_TO_XRF005_A */
   /* example: A_unlinked.dat */
   /* example: A_failed_linked.dat */

   act.sa_handler = sigCatch;
   sigemptyset(&act.sa_mask);
   act.sa_flags = SA_RESTART;
   if (sigaction(SIGTERM, &act, 0) != 0)
   {
      traceit("sigaction-TERM failed, error=%d\n", errno);
      traceit("audio_notify thread exiting...\n");
      pthread_exit(NULL);
   }
   if (sigaction(SIGINT, &act, 0) != 0)
   {
      traceit("sigaction-INT failed, error=%d\n", errno);
      traceit("audio_notify thread exiting...\n");
      pthread_exit(NULL);
   }
  
   memset(RADIO_ID, ' ', 20);
   RADIO_ID[20] = '\0';

   mod = notify_msg[0];

   if ((mod != 'A') && (mod != 'B') && (mod != 'C'))
   {
      traceit("Invalid module %c in %s\n", mod, notify_msg);
      pthread_exit(NULL);
   }

   p = strstr(notify_msg, ".dat");
   if (!p)
   {
      traceit("Incorrect filename in %s\n", notify_msg);
      pthread_exit(NULL);
   }

   if (p[4] == '_')
   {
      useTEXT = true;
      memcpy(RADIO_ID, p + 5, (strlen(p + 5) > 20)?20:strlen(p + 5));
      for (TEXT_idx = 0; TEXT_idx < 20; TEXT_idx++)
      {
         RADIO_ID[TEXT_idx] = toupper(RADIO_ID[TEXT_idx]);
         if (RADIO_ID[TEXT_idx] == '_')
            RADIO_ID[TEXT_idx] = ' ';
      }
      TEXT_idx = 0;
      p[4] = '\0';
   }
   else
      useTEXT = false;

   sleep(DELAY_BEFORE);

   memset(temp_file, '\0', sizeof(temp_file));
   snprintf(temp_file, FILENAME_MAX, "%s/%s", ANNOUNCE_DIR, notify_msg + 2);
   traceit("sending File:[%s], mod:[%c], RADIO_ID=[%s]\n", temp_file, mod, RADIO_ID);

   fp = fopen(temp_file, "rb");
   if (!fp)
   {
      traceit("Failed to open file %s for reading\n", temp_file);
      pthread_exit(NULL);
   }

   /* stupid DVTOOL + 4 byte num_of_records */
   nread = fread(dstar_buf, 10, 1, fp);
   if (nread != 1)
   {
      traceit("Cant read first 10 bytes from %s\n", temp_file);
      fclose(fp);
      pthread_exit(NULL);
   }
   if (memcmp(dstar_buf, "DVTOOL", 6) != 0)
   {
      traceit("DVTOOL keyword not found in %s\n", temp_file);
      fclose(fp);
      pthread_exit(NULL);
   }

   time(&tnow);
   aseed = tnow + pthread_self();

   while (keep_running)
   {
     /* 2 byte length */
     nread = fread(&rlen, 2, 1, fp);
     if (nread != 1)
        break;

     if (rlen == 56)
       streamid_raw = (::rand_r(&aseed) % 65535U) + 1U;
     else
     if (rlen == 27)
        ;
     else
     {
        traceit("Not 56-byte and not 27-byte in %s\n", temp_file);
        break;
     }

     nread = fread(dstar_buf, rlen, 1, fp);
     if (nread == 1)
     {
        if (memcmp(dstar_buf, "DSVT", 4) != 0)
        {
           traceit("DVST not found in %s\n", temp_file);
           break;
        }

        if (dstar_buf[8] != 0x20)
        {
           traceit("Not Voice type in %s\n", temp_file);
           break;
        }

        if (dstar_buf[4] == 0x10)
           ;
        else
        if (dstar_buf[4] == 0x20)
           ;
        else
        {
           traceit("Not a valid record type in %s\n", temp_file);
           break;
        }

        dstar_buf[12] = streamid_raw / 256U;
        dstar_buf[13] = streamid_raw % 256U;

        if (rlen == 56)
        {
           dstar_buf[15] = 0x00;

           memcpy(dstar_buf + 18, OWNER, CALL_SIZE);
           dstar_buf[25] = mod;

           memcpy(dstar_buf + 26, OWNER, CALL_SIZE);
           dstar_buf[33] = 'G';

           memcpy(dstar_buf + 34, "CQCQCQ  ", 8);

           memcpy(dstar_buf + 42, OWNER, CALL_SIZE);
           dstar_buf[48] = ' ';
           dstar_buf[49] = ' ';

           memcpy(dstar_buf + 50, "RPTR", 4);
           calcPFCS(dstar_buf, 56);
        }
        else
        {
           if (useTEXT)
           {
              if ((dstar_buf[24] != 0x55) ||
                  (dstar_buf[25] != 0x2d) ||
                  (dstar_buf[26] != 0x16))
              {
                 if (TEXT_idx == 0)
                 {
                    dstar_buf[24] = '@' ^ 0x70;
                    dstar_buf[25] = RADIO_ID[TEXT_idx++] ^ 0x4f;
                    dstar_buf[26] = RADIO_ID[TEXT_idx++] ^ 0x93;
                 }
                 else
                 if (TEXT_idx == 2)
                 {
                    dstar_buf[24] = RADIO_ID[TEXT_idx++] ^ 0x70;
                    dstar_buf[25] = RADIO_ID[TEXT_idx++] ^ 0x4f;
                    dstar_buf[26] = RADIO_ID[TEXT_idx++] ^ 0x93;
                 }
                 else
                 if (TEXT_idx == 5)
                 {
                    dstar_buf[24] = 'A' ^ 0x70;
                    dstar_buf[25] = RADIO_ID[TEXT_idx++] ^ 0x4f;
                    dstar_buf[26] = RADIO_ID[TEXT_idx++] ^ 0x93;
                 }
                 else
                 if (TEXT_idx == 7)
                 {
                    dstar_buf[24] = RADIO_ID[TEXT_idx++] ^ 0x70;
                    dstar_buf[25] = RADIO_ID[TEXT_idx++] ^ 0x4f;
                    dstar_buf[26] = RADIO_ID[TEXT_idx++] ^ 0x93;
                 }
                 else
                 if (TEXT_idx == 10)
                 {
                    dstar_buf[24] = 'B' ^ 0x70;
                    dstar_buf[25] = RADIO_ID[TEXT_idx++] ^ 0x4f;
                    dstar_buf[26] = RADIO_ID[TEXT_idx++] ^ 0x93;
                 }
                 else
                 if (TEXT_idx == 12)
                 {
                    dstar_buf[24] = RADIO_ID[TEXT_idx++] ^ 0x70;
                    dstar_buf[25] = RADIO_ID[TEXT_idx++] ^ 0x4f;
                    dstar_buf[26] = RADIO_ID[TEXT_idx++] ^ 0x93;
                 }
                 else
                 if (TEXT_idx == 15)
                 {
                    dstar_buf[24] = 'C' ^ 0x70;
                    dstar_buf[25] = RADIO_ID[TEXT_idx++] ^ 0x4f;
                    dstar_buf[26] = RADIO_ID[TEXT_idx++] ^ 0x93;
                 }
                 else
                 if (TEXT_idx == 17)
                 {
                    dstar_buf[24] = RADIO_ID[TEXT_idx++] ^ 0x70;
                    dstar_buf[25] = RADIO_ID[TEXT_idx++] ^ 0x4f;
                    dstar_buf[26] = RADIO_ID[TEXT_idx++] ^ 0x93;
                 }
                 else
                 {
                    dstar_buf[24] = 0x70;
                    dstar_buf[25] = 0x4f;
                    dstar_buf[26] = 0x93;
                 }
              }
           }
        }
        (void)sendto(ref_g2_sock, (char *)dstar_buf,rlen,0,
               (struct sockaddr *)&toLocalg2,sizeof(struct sockaddr_in));
     }
     nanos.tv_sec = 0;
     nanos.tv_nsec = DELAY_BETWEEN * 1000000;
     nanosleep(&nanos,0);
   }
   fclose(fp);
   traceit("finished sending File to mod:[%c]\n", mod);
   pthread_exit(NULL);
}

int main(int argc, char **argv)
{
   short i, j;
   struct sigaction act;
   int rc = 0;
   char unlink_request[CALL_SIZE + 3];
   inbound_type::iterator pos;
   inbound *inbound_ptr;

   char cmd_2_dcs[19];

   //v3.18

   unlink("/dstar/tmp/blocklinking-a");
   unlink("/dstar/tmp/blocklinking-b");
   unlink("/dstar/tmp/blocklinking-c");


   tzset();
   setvbuf(stdout, (char *)NULL, _IOLBF, 0);
   
   if (argc != 2)
   {
      traceit("Usage: ./g2_link g2_link.cfg\n");
      return 1;
   }
  
   rc = regcomp(&preg,
        "^(([1-9][A-Z])|([A-Z][0-9])|([A-Z][A-Z][0-9]))[0-9A-Z]*[A-Z][ ]*[ A-RT-Z]$",
        REG_EXTENDED | REG_NOSUB);
   if (rc != 0)
   {
      traceit("The IRC regular expression is NOT valid\n");
      return 1;
   }
  
   act.sa_handler = sigCatch;
   sigemptyset(&act.sa_mask);
   act.sa_flags = SA_RESTART;
   if (sigaction(SIGTERM, &act, 0) != 0)
   {
      traceit("sigaction-TERM failed, error=%d\n", errno);
      return 1;
   }
   if (sigaction(SIGINT, &act, 0) != 0)
   {
      traceit("sigaction-INT failed, error=%d\n", errno);
      return 1;
   }
    
   for (i = 0; i < 3; i++)
   {
      to_remote_g2[i].type = ' ';
      to_remote_g2[i].to_call[0] = '\0';
      memset(&(to_remote_g2[i].toDst4),0,sizeof(struct sockaddr_in));
      to_remote_g2[i].to_mod = ' ';
      to_remote_g2[i].to_mod = ' ';
      to_remote_g2[i].countdown = 0;
      to_remote_g2[i].is_connected = false;
      to_remote_g2[i].in_streamid[0] = 0x00;
      to_remote_g2[i].in_streamid[1] = 0x00;
      to_remote_g2[i].out_streamid[0] = 0x00;
      to_remote_g2[i].out_streamid[1] = 0x00;

      regen_hdr_for_plus_dongles[i].streamid[0] = 0x00;
      regen_hdr_for_plus_dongles[i].streamid[1] = 0x00;
   }

   ml_from_ref.ref_streamid[0] = ml_from_ref.ref_streamid[1] = 0x00;
   ml_from_ref.rptr_streamid[0][0] = ml_from_ref.rptr_streamid[0][1] = 0x00;
   ml_from_ref.rptr_streamid[1][0] = ml_from_ref.rptr_streamid[1][1] = 0x00;
   ml_from_ref_idx = 0;

   brd_from_xrf.xrf_streamid[0] = brd_from_xrf.xrf_streamid[1] = 0x00;
   brd_from_xrf.rptr_streamid[0][0] = brd_from_xrf.rptr_streamid[0][1] = 0x00;
   brd_from_xrf.rptr_streamid[1][0] = brd_from_xrf.rptr_streamid[1][1] = 0x00;
   brd_from_xrf_idx = 0;

   ml_from_rptr.from_rptr_streamid[0] = ml_from_rptr.from_rptr_streamid[1] = 0x00;
   ml_from_rptr.to_rptr_streamid[0][0] = ml_from_rptr.to_rptr_streamid[0][1] = 0x00;
   ml_from_rptr.to_rptr_streamid[1][0] = ml_from_rptr.to_rptr_streamid[1][1] = 0x00;
   ml_from_rptr_idx = 0;

   /* recording for echotest on local repeater modules */
   /* v3.18 for (i = 0; i < 3; i++)
   {
      recd[i].last_time = 0;
      recd[i].streamid[0] = 0x00;
      recd[i].streamid[1] = 0x00;
      recd[i].fd = -1;
      memset(recd[i].file, 0, sizeof(recd[i].file));
   } */


   do
   {
      /* process configuration file */
      if (!read_config(argv[1]))
      {
         traceit("Failed to process config file %s\n", argv[1]);
         break;
      }
      print_status_file();

      if (!resolve_plus())
         break; 

      /* Open DB */
      if (!load_gwys(GWYS))
         break;
 
      if (!load_valid_callsigns(VALID_CALLSIGNS))
         break;

      /* create our server */
      if (!srv_open())
      {
         traceit("srv_open() failed\n");
         break;
      }

      traceit("g2_link %s initialized...entering processing loop\n", VERSION);
      runit();
      traceit("Leaving processing loop...\n");

   } while (false);

   /* tell connected repeaters/reflectors */
   for (i = 0; i < 3; i++)
   {
      if (to_remote_g2[i].to_call[0] != '\0')
      {
         if (to_remote_g2[i].type == 'p')
         {
            queryCommand[0] = 0x05;
            queryCommand[1] = 0x00;
            queryCommand[2] = 0x18;
            queryCommand[3] = ((to_remote_g2[i].from_mod - 'A') << 4) | (to_remote_g2[i].to_mod - 'A');
            queryCommand[4] = 0x00;
            for (j = 0; j < 3; j++)
               sendto(ref_g2_sock,(char *)queryCommand,5,0,
                      (struct sockaddr *)&(to_remote_g2[i].toDst4),
                      sizeof(to_remote_g2[i].toDst4));
         }
         else
         if (to_remote_g2[i].type == 'x')
         {
            strcpy(unlink_request, OWNER);
            unlink_request[8] = to_remote_g2[i].from_mod;
            unlink_request[9] = ' ';
            unlink_request[10] = '\0';
            for (j = 0; j < 5; j++)
               sendto(xrf_g2_sock,unlink_request, CALL_SIZE + 3,0,
                      (struct sockaddr *)&(to_remote_g2[i].toDst4),
                      sizeof(to_remote_g2[i].toDst4));
         }
         else
         {
            strcpy(cmd_2_dcs, OWNER);
            cmd_2_dcs[8] = to_remote_g2[i].from_mod;
            cmd_2_dcs[9] = ' ';
            cmd_2_dcs[10] = '\0';
            memcpy(cmd_2_dcs + 11, to_remote_g2[i].to_call, 8);

            for (j = 0; j < 5; j++)
               sendto(dcs_g2_sock, cmd_2_dcs, 19,0,
                (struct sockaddr *)&(to_remote_g2[i].toDst4),
                sizeof(to_remote_g2[i].toDst4));
         }
      }
      to_remote_g2[i].type = ' ';
      to_remote_g2[i].to_call[0] = '\0';
      memset(&(to_remote_g2[i].toDst4),0,sizeof(struct sockaddr_in));
      to_remote_g2[i].from_mod = ' ';
      to_remote_g2[i].to_mod = ' ';
      to_remote_g2[i].countdown = 0;
      to_remote_g2[i].is_connected = false;
      to_remote_g2[i].in_streamid[0] = 0x00;
      to_remote_g2[i].in_streamid[1] = 0x00;
      to_remote_g2[i].out_streamid[0] = 0x00;
      to_remote_g2[i].out_streamid[1] = 0x00;
   }

   /* tell dongles we are down */
   queryCommand[0] = 5;
   queryCommand[1] = 0;
   queryCommand[2] = 24;
   queryCommand[3] = 0;
   queryCommand[4] = 0;
   for (pos = inbound_list.begin(); pos != inbound_list.end(); pos++)
   {
      inbound_ptr = (inbound *)pos->second;
      sendto(ref_g2_sock,(char *)queryCommand,5,0,
             (struct sockaddr *)&(inbound_ptr->sin),
             sizeof(struct sockaddr_in));
   }
   inbound_list.clear();


   /* v3.18 - remove the blocking files */

   unlink("/dstar/tmp/blocklinking-a");
   unlink("/dstar/tmp/blocklinking-b");
   unlink("/dstar/tmp/blocklinking-c");

   print_status_file();
   srv_close();

   /* close/remove echotest files */
   /* v3.18 for (i = 0; i < 3; i++)
   {
      recd[i].last_time = 0;
      recd[i].streamid[0] = 0x00;
      recd[i].streamid[1] = 0x00;
      if (recd[i].fd >= 0)
      {
         close(recd[i].fd);
         unlink(recd[i].file);
      }
   } */


   traceit("g2_link exiting\n");
   return 0;
}
