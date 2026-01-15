/* Generated from crypto-ffi.scm by the CHICKEN compiler
   http://www.call-cc.org
   Version 5.4.0 (rev 1a1d1495)
   macosx-unix-clang-arm64 [ 64bit dload ptables ]
   command line: crypto-ffi.scm -output-file crypto-ffi.c -dynamic -feature chicken-compile-shared -emit-all-import-libraries -optimize-level 2
   uses: eval srfi-4 lolevel extras library
*/
#include "chicken.h"

#include <sodium.h>

static C_PTABLE_ENTRY *create_ptable(void);
C_noret_decl(C_eval_toplevel)
C_externimport void C_ccall C_eval_toplevel(C_word c,C_word *av) C_noret;
C_noret_decl(C_srfi_2d4_toplevel)
C_externimport void C_ccall C_srfi_2d4_toplevel(C_word c,C_word *av) C_noret;
C_noret_decl(C_lolevel_toplevel)
C_externimport void C_ccall C_lolevel_toplevel(C_word c,C_word *av) C_noret;
C_noret_decl(C_extras_toplevel)
C_externimport void C_ccall C_extras_toplevel(C_word c,C_word *av) C_noret;
C_noret_decl(C_library_toplevel)
C_externimport void C_ccall C_library_toplevel(C_word c,C_word *av) C_noret;

static C_TLS C_word lf[101];
static double C_possibly_force_alignment;
static C_char C_TLS li0[] C_aligned={C_lihdr(0,0,24),40,99,114,121,112,116,111,45,102,102,105,35,115,111,100,105,117,109,45,105,110,105,116,41};
static C_char C_TLS li1[] C_aligned={C_lihdr(0,0,63),40,99,114,121,112,116,111,45,102,102,105,35,101,100,50,53,53,49,57,45,107,101,121,112,97,105,114,33,32,115,99,104,101,109,101,45,112,111,105,110,116,101,114,50,57,32,115,99,104,101,109,101,45,112,111,105,110,116,101,114,51,48,41,0};
static C_char C_TLS li2[] C_aligned={C_lihdr(0,0,28),40,99,114,121,112,116,111,45,102,102,105,35,101,100,50,53,53,49,57,45,107,101,121,112,97,105,114,41,0,0,0,0};
static C_char C_TLS li3[] C_aligned={C_lihdr(0,0,12),40,100,111,108,111,111,112,52,56,32,105,41,0,0,0,0};
static C_char C_TLS li4[] C_aligned={C_lihdr(0,0,48),40,99,114,121,112,116,111,45,102,102,105,35,101,100,50,53,53,49,57,45,115,101,99,114,101,116,45,116,111,45,112,117,98,108,105,99,32,115,101,99,114,101,116,45,107,101,121,41};
static C_char C_TLS li5[] C_aligned={C_lihdr(0,0,44),40,99,114,121,112,116,111,45,102,102,105,35,101,100,50,53,53,49,57,45,115,105,103,110,32,115,101,99,114,101,116,45,107,101,121,32,109,101,115,115,97,103,101,41,0,0,0,0};
static C_char C_TLS li6[] C_aligned={C_lihdr(0,0,56),40,99,114,121,112,116,111,45,102,102,105,35,101,100,50,53,53,49,57,45,118,101,114,105,102,121,32,112,117,98,108,105,99,45,107,101,121,32,109,101,115,115,97,103,101,32,115,105,103,110,97,116,117,114,101,41};
static C_char C_TLS li7[] C_aligned={C_lihdr(0,0,29),40,99,114,121,112,116,111,45,102,102,105,35,115,104,97,50,53,54,45,104,97,115,104,32,100,97,116,97,41,0,0,0};
static C_char C_TLS li8[] C_aligned={C_lihdr(0,0,29),40,99,114,121,112,116,111,45,102,102,105,35,115,104,97,53,49,50,45,104,97,115,104,32,100,97,116,97,41,0,0,0};
static C_char C_TLS li9[] C_aligned={C_lihdr(0,0,30),40,99,114,121,112,116,111,45,102,102,105,35,98,108,97,107,101,50,98,45,104,97,115,104,32,100,97,116,97,41,0,0};
static C_char C_TLS li10[] C_aligned={C_lihdr(0,0,27),40,99,114,121,112,116,111,45,102,102,105,35,114,97,110,100,111,109,45,98,121,116,101,115,32,110,41,0,0,0,0,0};
static C_char C_TLS li11[] C_aligned={C_lihdr(0,0,22),40,99,114,121,112,116,111,45,102,102,105,35,114,97,110,100,111,109,45,117,56,41,0,0};
static C_char C_TLS li12[] C_aligned={C_lihdr(0,0,23),40,99,114,121,112,116,111,45,102,102,105,35,114,97,110,100,111,109,45,117,51,50,41,0};
static C_char C_TLS li13[] C_aligned={C_lihdr(0,0,39),40,99,114,121,112,116,111,45,102,102,105,35,114,97,110,100,111,109,45,117,110,105,102,111,114,109,32,117,112,112,101,114,45,98,111,117,110,100,41,0};
static C_char C_TLS li14[] C_aligned={C_lihdr(0,0,27),40,99,114,121,112,116,111,45,102,102,105,35,101,110,116,114,111,112,121,45,115,116,97,116,117,115,41,0,0,0,0,0};
static C_char C_TLS li15[] C_aligned={C_lihdr(0,0,25),40,99,114,121,112,116,111,45,102,102,105,35,109,101,109,122,101,114,111,33,32,98,117,102,41,0,0,0,0,0,0,0};
static C_char C_TLS li16[] C_aligned={C_lihdr(0,0,40),40,99,114,121,112,116,111,45,102,102,105,35,97,114,103,111,110,50,105,100,45,104,97,115,104,32,112,97,115,115,119,111,114,100,32,115,97,108,116,41};
static C_char C_TLS li17[] C_aligned={C_lihdr(0,0,50),40,99,114,121,112,116,111,45,102,102,105,35,115,101,99,114,101,116,98,111,120,45,101,110,99,114,121,112,116,32,112,108,97,105,110,116,101,120,116,32,110,111,110,99,101,32,107,101,121,41,0,0,0,0,0,0};
static C_char C_TLS li18[] C_aligned={C_lihdr(0,0,51),40,99,114,121,112,116,111,45,102,102,105,35,115,101,99,114,101,116,98,111,120,45,100,101,99,114,121,112,116,32,99,105,112,104,101,114,116,101,120,116,32,110,111,110,99,101,32,107,101,121,41,0,0,0,0,0};
static C_char C_TLS li19[] C_aligned={C_lihdr(0,0,27),40,99,114,121,112,116,111,45,102,102,105,35,120,50,53,53,49,57,45,107,101,121,112,97,105,114,41,0,0,0,0,0};
static C_char C_TLS li20[] C_aligned={C_lihdr(0,0,52),40,99,114,121,112,116,111,45,102,102,105,35,120,50,53,53,49,57,45,115,99,97,108,97,114,109,117,108,116,32,115,101,99,114,101,116,45,107,101,121,32,112,117,98,108,105,99,45,107,101,121,41,0,0,0,0};
static C_char C_TLS li21[] C_aligned={C_lihdr(0,0,26),40,99,114,121,112,116,111,45,102,102,105,35,103,102,50,53,54,45,97,100,100,32,97,32,98,41,0,0,0,0,0,0};
static C_char C_TLS li22[] C_aligned={C_lihdr(0,0,26),40,99,114,121,112,116,111,45,102,102,105,35,103,102,50,53,54,45,109,117,108,32,97,32,98,41,0,0,0,0,0,0};
static C_char C_TLS li23[] C_aligned={C_lihdr(0,0,26),40,99,114,121,112,116,111,45,102,102,105,35,103,102,50,53,54,45,100,105,118,32,97,32,98,41,0,0,0,0,0,0};
static C_char C_TLS li24[] C_aligned={C_lihdr(0,0,28),40,99,114,121,112,116,111,45,102,102,105,35,115,104,97,109,105,114,45,115,104,97,114,101,63,32,120,41,0,0,0,0};
static C_char C_TLS li25[] C_aligned={C_lihdr(0,0,23),40,99,114,121,112,116,111,45,102,102,105,35,115,104,97,114,101,45,105,100,32,120,41,0};
static C_char C_TLS li26[] C_aligned={C_lihdr(0,0,30),40,99,114,121,112,116,111,45,102,102,105,35,115,104,97,114,101,45,116,104,114,101,115,104,111,108,100,32,120,41,0,0};
static C_char C_TLS li27[] C_aligned={C_lihdr(0,0,22),40,99,114,121,112,116,111,45,102,102,105,35,115,104,97,114,101,45,120,32,120,41,0,0};
static C_char C_TLS li28[] C_aligned={C_lihdr(0,0,22),40,99,114,121,112,116,111,45,102,102,105,35,115,104,97,114,101,45,121,32,120,41,0,0};
static C_char C_TLS li29[] C_aligned={C_lihdr(0,0,13),40,100,111,108,111,111,112,53,48,56,32,105,41,0,0,0};
static C_char C_TLS li30[] C_aligned={C_lihdr(0,0,15),40,108,111,111,112,32,105,32,114,101,115,117,108,116,41,0};
static C_char C_TLS li31[] C_aligned={C_lihdr(0,0,21),40,100,111,108,111,111,112,53,49,55,32,115,104,97,114,101,45,110,117,109,41,0,0,0};
static C_char C_TLS li32[] C_aligned={C_lihdr(0,0,13),40,100,111,108,111,111,112,53,49,54,32,105,41,0,0,0};
static C_char C_TLS li33[] C_aligned={C_lihdr(0,0,20),40,100,111,108,111,111,112,53,48,55,32,98,121,116,101,45,105,100,120,41,0,0,0,0};
static C_char C_TLS li34[] C_aligned={C_lihdr(0,0,13),40,100,111,108,111,111,112,53,48,54,32,105,41,0,0,0};
static C_char C_TLS li35[] C_aligned={C_lihdr(0,0,7),40,97,50,50,49,48,41,0};
static C_char C_TLS li36[] C_aligned={C_lihdr(0,0,7),40,97,50,50,49,51,41,0};
static C_char C_TLS li37[] C_aligned={C_lihdr(0,0,39),40,99,114,121,112,116,111,45,102,102,105,35,115,104,97,109,105,114,45,115,112,108,105,116,32,115,101,99,114,101,116,32,46,32,114,101,115,116,41,0};
static C_char C_TLS li38[] C_aligned={C_lihdr(0,0,13),40,100,111,108,111,111,112,53,54,57,32,106,41,0,0,0};
static C_char C_TLS li39[] C_aligned={C_lihdr(0,0,13),40,100,111,108,111,111,112,53,54,51,32,105,41,0,0,0};
static C_char C_TLS li40[] C_aligned={C_lihdr(0,0,20),40,100,111,108,111,111,112,53,53,57,32,98,121,116,101,45,105,100,120,41,0,0,0,0};
static C_char C_TLS li41[] C_aligned={C_lihdr(0,0,38),40,99,114,121,112,116,111,45,102,102,105,35,115,104,97,109,105,114,45,114,101,99,111,110,115,116,114,117,99,116,32,115,104,97,114,101,115,41,0,0};
static C_char C_TLS li42[] C_aligned={C_lihdr(0,0,13),40,100,111,108,111,111,112,52,51,48,32,105,41,0,0,0};
static C_char C_TLS li43[] C_aligned={C_lihdr(0,0,13),40,100,111,108,111,111,112,52,51,50,32,105,41,0,0,0};
static C_char C_TLS li44[] C_aligned={C_lihdr(0,0,10),40,116,111,112,108,101,118,101,108,41,0,0,0,0,0,0};


/* from k1624 */
C_regparm static C_word C_fcall stub390(C_word C_buf,C_word C_a0,C_word C_a1,C_word C_a2){
C_word C_r=C_SCHEME_UNDEFINED,*C_a=(C_word*)C_buf;
void * t0=(void * )C_data_pointer_or_null(C_a0);
void * t1=(void * )C_data_pointer_or_null(C_a1);
void * t2=(void * )C_data_pointer_or_null(C_a2);
C_r=C_fix((C_word)crypto_scalarmult(t0,t1,t2));
return C_r;}

/* from k1592 */
C_regparm static C_word C_fcall stub371(C_word C_buf,C_word C_a0,C_word C_a1){
C_word C_r=C_SCHEME_UNDEFINED,*C_a=(C_word*)C_buf;
void * t0=(void * )C_data_pointer_or_null(C_a0);
void * t1=(void * )C_data_pointer_or_null(C_a1);
C_r=C_fix((C_word)crypto_box_keypair(t0,t1));
return C_r;}

/* from k1535 */
C_regparm static C_word C_fcall stub336(C_word C_buf,C_word C_a0,C_word C_a1,C_word C_a2,C_word C_a3,C_word C_a4){
C_word C_r=C_SCHEME_UNDEFINED,*C_a=(C_word*)C_buf;
void * t0=(void * )C_data_pointer_or_null(C_a0);
void * t1=(void * )C_data_pointer_or_null(C_a1);
unsigned int t2=(unsigned int )C_num_to_unsigned_int(C_a2);
void * t3=(void * )C_data_pointer_or_null(C_a3);
void * t4=(void * )C_data_pointer_or_null(C_a4);
C_r=C_fix((C_word)crypto_secretbox_open_easy(t0,t1,t2,t3,t4));
return C_r;}

/* from k1475 */
C_regparm static C_word C_fcall stub306(C_word C_buf,C_word C_a0,C_word C_a1,C_word C_a2,C_word C_a3,C_word C_a4){
C_word C_r=C_SCHEME_UNDEFINED,*C_a=(C_word*)C_buf;
void * t0=(void * )C_data_pointer_or_null(C_a0);
void * t1=(void * )C_data_pointer_or_null(C_a1);
unsigned int t2=(unsigned int )C_num_to_unsigned_int(C_a2);
void * t3=(void * )C_data_pointer_or_null(C_a3);
void * t4=(void * )C_data_pointer_or_null(C_a4);
C_r=C_fix((C_word)crypto_secretbox_easy(t0,t1,t2,t3,t4));
return C_r;}

/* from k1409 */
C_regparm static C_word C_fcall stub272(C_word C_buf,C_word C_a0,C_word C_a1,C_word C_a2,C_word C_a3,C_word C_a4,C_word C_a5,C_word C_a6,C_word C_a7){
C_word C_r=C_SCHEME_UNDEFINED,*C_a=(C_word*)C_buf;
void * t0=(void * )C_data_pointer_or_null(C_a0);
unsigned int t1=(unsigned int )C_num_to_unsigned_int(C_a1);
void * t2=(void * )C_data_pointer_or_null(C_a2);
unsigned int t3=(unsigned int )C_num_to_unsigned_int(C_a3);
void * t4=(void * )C_data_pointer_or_null(C_a4);
unsigned int t5=(unsigned int )C_num_to_unsigned_int(C_a5);
unsigned int t6=(unsigned int )C_num_to_unsigned_int(C_a6);
int t7=(int )C_unfix(C_a7);
C_r=C_fix((C_word)crypto_pwhash(t0,t1,t2,t3,t4,t5,t6,t7));
return C_r;}

/* from k1355 */
C_regparm static C_word C_fcall stub249(C_word C_buf,C_word C_a0,C_word C_a1){
C_word C_r=C_SCHEME_UNDEFINED,*C_a=(C_word*)C_buf;
void * t0=(void * )C_data_pointer_or_null(C_a0);
unsigned int t1=(unsigned int )C_num_to_unsigned_int(C_a1);
sodium_memzero(t0,t1);
return C_r;}

/* from g231 */
C_regparm static C_word C_fcall stub233(C_word C_buf){
C_word C_r=C_SCHEME_UNDEFINED,*C_a=(C_word*)C_buf;
C_r=C_mpointer(&C_a,(void*)randombytes_implementation_name());
return C_r;}

/* from k1299 */
C_regparm static C_word C_fcall stub226(C_word C_buf,C_word C_a0){
C_word C_r=C_SCHEME_UNDEFINED,*C_a=(C_word*)C_buf;
C_u32 t0=(C_u32 )C_unfix(C_a0);
C_r=C_fix(C_MOST_POSITIVE_FIXNUM&(C_word)randombytes_uniform(t0));
return C_r;}

/* from g217 */
C_regparm static C_word C_fcall stub219(C_word C_buf){
C_word C_r=C_SCHEME_UNDEFINED,*C_a=(C_word*)C_buf;
C_r=C_fix(C_MOST_POSITIVE_FIXNUM&(C_word)randombytes_random());
return C_r;}

/* from k1265 */
C_regparm static C_word C_fcall stub207(C_word C_buf,C_word C_a0,C_word C_a1){
C_word C_r=C_SCHEME_UNDEFINED,*C_a=(C_word*)C_buf;
void * t0=(void * )C_data_pointer_or_null(C_a0);
unsigned int t1=(unsigned int )C_num_to_unsigned_int(C_a1);
randombytes_buf(t0,t1);
return C_r;}

/* from k1242 */
C_regparm static C_word C_fcall stub193(C_word C_buf,C_word C_a0,C_word C_a1){
C_word C_r=C_SCHEME_UNDEFINED,*C_a=(C_word*)C_buf;
void * t0=(void * )C_data_pointer_or_null(C_a0);
unsigned int t1=(unsigned int )C_num_to_unsigned_int(C_a1);
randombytes_buf(t0,t1);
return C_r;}

/* from k1194 */
C_regparm static C_word C_fcall stub161(C_word C_buf,C_word C_a0,C_word C_a1,C_word C_a2,C_word C_a3,C_word C_a4,C_word C_a5){
C_word C_r=C_SCHEME_UNDEFINED,*C_a=(C_word*)C_buf;
void * t0=(void * )C_data_pointer_or_null(C_a0);
unsigned int t1=(unsigned int )C_num_to_unsigned_int(C_a1);
void * t2=(void * )C_data_pointer_or_null(C_a2);
unsigned int t3=(unsigned int )C_num_to_unsigned_int(C_a3);
void * t4=(void * )C_data_pointer_or_null(C_a4);
unsigned int t5=(unsigned int )C_num_to_unsigned_int(C_a5);
C_r=C_fix((C_word)crypto_generichash(t0,t1,t2,t3,t4,t5));
return C_r;}

/* from k1138 */
C_regparm static C_word C_fcall stub137(C_word C_buf,C_word C_a0,C_word C_a1,C_word C_a2){
C_word C_r=C_SCHEME_UNDEFINED,*C_a=(C_word*)C_buf;
void * t0=(void * )C_data_pointer_or_null(C_a0);
void * t1=(void * )C_data_pointer_or_null(C_a1);
unsigned int t2=(unsigned int )C_num_to_unsigned_int(C_a2);
C_r=C_fix((C_word)crypto_hash_sha512(t0,t1,t2));
return C_r;}

/* from k1095 */
C_regparm static C_word C_fcall stub117(C_word C_buf,C_word C_a0,C_word C_a1,C_word C_a2){
C_word C_r=C_SCHEME_UNDEFINED,*C_a=(C_word*)C_buf;
void * t0=(void * )C_data_pointer_or_null(C_a0);
void * t1=(void * )C_data_pointer_or_null(C_a1);
unsigned int t2=(unsigned int )C_num_to_unsigned_int(C_a2);
C_r=C_fix((C_word)crypto_hash_sha256(t0,t1,t2));
return C_r;}

/* from k1046 */
C_regparm static C_word C_fcall stub95(C_word C_buf,C_word C_a0,C_word C_a1,C_word C_a2,C_word C_a3){
C_word C_r=C_SCHEME_UNDEFINED,*C_a=(C_word*)C_buf;
void * t0=(void * )C_data_pointer_or_null(C_a0);
void * t1=(void * )C_data_pointer_or_null(C_a1);
unsigned int t2=(unsigned int )C_num_to_unsigned_int(C_a2);
void * t3=(void * )C_data_pointer_or_null(C_a3);
C_r=C_fix((C_word)crypto_sign_verify_detached(t0,t1,t2,t3));
return C_r;}

/* from k996 */
C_regparm static C_word C_fcall stub66(C_word C_buf,C_word C_a0,C_word C_a1,C_word C_a2,C_word C_a3,C_word C_a4){
C_word C_r=C_SCHEME_UNDEFINED,*C_a=(C_word*)C_buf;
void * t0=(void * )C_data_pointer_or_null(C_a0);
void * t1=(void * )C_data_pointer_or_null(C_a1);
void * t2=(void * )C_data_pointer_or_null(C_a2);
unsigned int t3=(unsigned int )C_num_to_unsigned_int(C_a3);
void * t4=(void * )C_data_pointer_or_null(C_a4);
C_r=C_fix((C_word)crypto_sign_detached(t0,t1,t2,t3,t4));
return C_r;}

/* from k899 */
C_regparm static C_word C_fcall stub31(C_word C_buf,C_word C_a0,C_word C_a1){
C_word C_r=C_SCHEME_UNDEFINED,*C_a=(C_word*)C_buf;
void * t0=(void * )C_data_pointer_or_null(C_a0);
void * t1=(void * )C_data_pointer_or_null(C_a1);
C_r=C_fix((C_word)crypto_sign_keypair(t0,t1));
return C_r;}

/* from crypto-ffi#sodium-init in k880 in k877 in k874 in k871 in k868 in k865 */
C_regparm static C_word C_fcall stub26(C_word C_buf){
C_word C_r=C_SCHEME_UNDEFINED,*C_a=(C_word*)C_buf;
C_r=C_fix((C_word)sodium_init());
return C_r;}

C_noret_decl(f_1018)
static void C_ccall f_1018(C_word c,C_word *av) C_noret;
C_noret_decl(f_1026)
static void C_ccall f_1026(C_word c,C_word *av) C_noret;
C_noret_decl(f_1030)
static void C_ccall f_1030(C_word c,C_word *av) C_noret;
C_noret_decl(f_1068)
static void C_ccall f_1068(C_word c,C_word *av) C_noret;
C_noret_decl(f_1076)
static void C_ccall f_1076(C_word c,C_word *av) C_noret;
C_noret_decl(f_1080)
static void C_ccall f_1080(C_word c,C_word *av) C_noret;
C_noret_decl(f_1083)
static void C_ccall f_1083(C_word c,C_word *av) C_noret;
C_noret_decl(f_1111)
static void C_ccall f_1111(C_word c,C_word *av) C_noret;
C_noret_decl(f_1119)
static void C_ccall f_1119(C_word c,C_word *av) C_noret;
C_noret_decl(f_1123)
static void C_ccall f_1123(C_word c,C_word *av) C_noret;
C_noret_decl(f_1126)
static void C_ccall f_1126(C_word c,C_word *av) C_noret;
C_noret_decl(f_1154)
static void C_ccall f_1154(C_word c,C_word *av) C_noret;
C_noret_decl(f_1163)
static void C_ccall f_1163(C_word c,C_word *av) C_noret;
C_noret_decl(f_1167)
static void C_ccall f_1167(C_word c,C_word *av) C_noret;
C_noret_decl(f_1170)
static void C_ccall f_1170(C_word c,C_word *av) C_noret;
C_noret_decl(f_1215)
static void C_ccall f_1215(C_word c,C_word *av) C_noret;
C_noret_decl(f_1230)
static void C_ccall f_1230(C_word c,C_word *av) C_noret;
C_noret_decl(f_1234)
static void C_ccall f_1234(C_word c,C_word *av) C_noret;
C_noret_decl(f_1253)
static void C_ccall f_1253(C_word c,C_word *av) C_noret;
C_noret_decl(f_1257)
static void C_ccall f_1257(C_word c,C_word *av) C_noret;
C_noret_decl(f_1277)
static void C_ccall f_1277(C_word c,C_word *av) C_noret;
C_noret_decl(f_1284)
static void C_ccall f_1284(C_word c,C_word *av) C_noret;
C_noret_decl(f_1286)
static void C_ccall f_1286(C_word c,C_word *av) C_noret;
C_noret_decl(f_1294)
static void C_ccall f_1294(C_word c,C_word *av) C_noret;
C_noret_decl(f_1306)
static void C_ccall f_1306(C_word c,C_word *av) C_noret;
C_noret_decl(f_1316)
static void C_ccall f_1316(C_word c,C_word *av) C_noret;
C_noret_decl(f_1346)
static void C_ccall f_1346(C_word c,C_word *av) C_noret;
C_noret_decl(f_1368)
static void C_ccall f_1368(C_word c,C_word *av) C_noret;
C_noret_decl(f_1370)
static void C_ccall f_1370(C_word c,C_word *av) C_noret;
C_noret_decl(f_1374)
static void C_ccall f_1374(C_word c,C_word *av) C_noret;
C_noret_decl(f_1377)
static void C_ccall f_1377(C_word c,C_word *av) C_noret;
C_noret_decl(f_1440)
static void C_ccall f_1440(C_word c,C_word *av) C_noret;
C_noret_decl(f_1448)
static void C_ccall f_1448(C_word c,C_word *av) C_noret;
C_noret_decl(f_1452)
static void C_ccall f_1452(C_word c,C_word *av) C_noret;
C_noret_decl(f_1455)
static void C_ccall f_1455(C_word c,C_word *av) C_noret;
C_noret_decl(f_1508)
static void C_ccall f_1508(C_word c,C_word *av) C_noret;
C_noret_decl(f_1512)
static void C_ccall f_1512(C_word c,C_word *av) C_noret;
C_noret_decl(f_1515)
static void C_ccall f_1515(C_word c,C_word *av) C_noret;
C_noret_decl(f_1577)
static void C_ccall f_1577(C_word c,C_word *av) C_noret;
C_noret_decl(f_1581)
static void C_ccall f_1581(C_word c,C_word *av) C_noret;
C_noret_decl(f_1584)
static void C_ccall f_1584(C_word c,C_word *av) C_noret;
C_noret_decl(f_1608)
static void C_ccall f_1608(C_word c,C_word *av) C_noret;
C_noret_decl(f_1612)
static void C_ccall f_1612(C_word c,C_word *av) C_noret;
C_noret_decl(f_1747)
static void C_ccall f_1747(C_word c,C_word *av) C_noret;
C_noret_decl(f_1751)
static void C_ccall f_1751(C_word c,C_word *av) C_noret;
C_noret_decl(f_1757)
static void C_ccall f_1757(C_word c,C_word *av) C_noret;
C_noret_decl(f_1762)
static void C_fcall f_1762(C_word t0,C_word t1,C_word t2) C_noret;
C_noret_decl(f_1789)
static void C_fcall f_1789(C_word t0,C_word t1,C_word t2) C_noret;
C_noret_decl(f_1834)
static void C_ccall f_1834(C_word c,C_word *av) C_noret;
C_noret_decl(f_1836)
static void C_ccall f_1836(C_word c,C_word *av) C_noret;
C_noret_decl(f_1842)
static void C_ccall f_1842(C_word c,C_word *av) C_noret;
C_noret_decl(f_1876)
static void C_ccall f_1876(C_word c,C_word *av) C_noret;
C_noret_decl(f_1918)
static void C_fcall f_1918(C_word t0,C_word t1,C_word t2,C_word t3) C_noret;
C_noret_decl(f_1936)
static void C_ccall f_1936(C_word c,C_word *av) C_noret;
C_noret_decl(f_1944)
static void C_ccall f_1944(C_word c,C_word *av) C_noret;
C_noret_decl(f_1957)
static void C_ccall f_1957(C_word c,C_word *av) C_noret;
C_noret_decl(f_1963)
static void C_ccall f_1963(C_word c,C_word *av) C_noret;
C_noret_decl(f_1972)
static void C_ccall f_1972(C_word c,C_word *av) C_noret;
C_noret_decl(f_1981)
static void C_ccall f_1981(C_word c,C_word *av) C_noret;
C_noret_decl(f_1990)
static void C_ccall f_1990(C_word c,C_word *av) C_noret;
C_noret_decl(f_1999)
static void C_ccall f_1999(C_word c,C_word *av) C_noret;
C_noret_decl(f_2003)
static void C_ccall f_2003(C_word c,C_word *av) C_noret;
C_noret_decl(f_2006)
static void C_ccall f_2006(C_word c,C_word *av) C_noret;
C_noret_decl(f_2009)
static void C_ccall f_2009(C_word c,C_word *av) C_noret;
C_noret_decl(f_2012)
static void C_ccall f_2012(C_word c,C_word *av) C_noret;
C_noret_decl(f_2015)
static void C_ccall f_2015(C_word c,C_word *av) C_noret;
C_noret_decl(f_2021)
static void C_ccall f_2021(C_word c,C_word *av) C_noret;
C_noret_decl(f_2024)
static void C_ccall f_2024(C_word c,C_word *av) C_noret;
C_noret_decl(f_2027)
static void C_ccall f_2027(C_word c,C_word *av) C_noret;
C_noret_decl(f_2030)
static void C_ccall f_2030(C_word c,C_word *av) C_noret;
C_noret_decl(f_2035)
static void C_fcall f_2035(C_word t0,C_word t1,C_word t2) C_noret;
C_noret_decl(f_2060)
static void C_ccall f_2060(C_word c,C_word *av) C_noret;
C_noret_decl(f_2068)
static void C_ccall f_2068(C_word c,C_word *av) C_noret;
C_noret_decl(f_2076)
static void C_ccall f_2076(C_word c,C_word *av) C_noret;
C_noret_decl(f_2080)
static void C_ccall f_2080(C_word c,C_word *av) C_noret;
C_noret_decl(f_2086)
static void C_fcall f_2086(C_word t0,C_word t1,C_word t2) C_noret;
C_noret_decl(f_2096)
static void C_ccall f_2096(C_word c,C_word *av) C_noret;
C_noret_decl(f_2102)
static void C_ccall f_2102(C_word c,C_word *av) C_noret;
C_noret_decl(f_2105)
static void C_ccall f_2105(C_word c,C_word *av) C_noret;
C_noret_decl(f_2114)
static void C_fcall f_2114(C_word t0,C_word t1,C_word t2) C_noret;
C_noret_decl(f_2139)
static void C_ccall f_2139(C_word c,C_word *av) C_noret;
C_noret_decl(f_2143)
static void C_ccall f_2143(C_word c,C_word *av) C_noret;
C_noret_decl(f_2149)
static void C_fcall f_2149(C_word t0,C_word t1,C_word t2) C_noret;
C_noret_decl(f_2170)
static void C_ccall f_2170(C_word c,C_word *av) C_noret;
C_noret_decl(f_2176)
static void C_fcall f_2176(C_word t0,C_word t1,C_word t2) C_noret;
C_noret_decl(f_2197)
static void C_ccall f_2197(C_word c,C_word *av) C_noret;
C_noret_decl(f_2211)
static void C_ccall f_2211(C_word c,C_word *av) C_noret;
C_noret_decl(f_2214)
static void C_ccall f_2214(C_word c,C_word *av) C_noret;
C_noret_decl(f_2217)
static void C_ccall f_2217(C_word c,C_word *av) C_noret;
C_noret_decl(f_2221)
static void C_ccall f_2221(C_word c,C_word *av) C_noret;
C_noret_decl(f_2224)
static void C_ccall f_2224(C_word c,C_word *av) C_noret;
C_noret_decl(f_2230)
static void C_ccall f_2230(C_word c,C_word *av) C_noret;
C_noret_decl(f_2233)
static void C_ccall f_2233(C_word c,C_word *av) C_noret;
C_noret_decl(f_2236)
static void C_ccall f_2236(C_word c,C_word *av) C_noret;
C_noret_decl(f_2239)
static void C_ccall f_2239(C_word c,C_word *av) C_noret;
C_noret_decl(f_2242)
static void C_ccall f_2242(C_word c,C_word *av) C_noret;
C_noret_decl(f_2247)
static void C_fcall f_2247(C_word t0,C_word t1,C_word t2) C_noret;
C_noret_decl(f_2257)
static void C_ccall f_2257(C_word c,C_word *av) C_noret;
C_noret_decl(f_2269)
static void C_fcall f_2269(C_word t0,C_word t1,C_word t2) C_noret;
C_noret_decl(f_2279)
static void C_ccall f_2279(C_word c,C_word *av) C_noret;
C_noret_decl(f_2285)
static void C_ccall f_2285(C_word c,C_word *av) C_noret;
C_noret_decl(f_2289)
static void C_ccall f_2289(C_word c,C_word *av) C_noret;
C_noret_decl(f_2300)
static void C_ccall f_2300(C_word c,C_word *av) C_noret;
C_noret_decl(f_2302)
static void C_fcall f_2302(C_word t0,C_word t1,C_word t2) C_noret;
C_noret_decl(f_2325)
static void C_ccall f_2325(C_word c,C_word *av) C_noret;
C_noret_decl(f_2329)
static void C_ccall f_2329(C_word c,C_word *av) C_noret;
C_noret_decl(f_2333)
static void C_ccall f_2333(C_word c,C_word *av) C_noret;
C_noret_decl(f_2337)
static void C_ccall f_2337(C_word c,C_word *av) C_noret;
C_noret_decl(f_2349)
static void C_ccall f_2349(C_word c,C_word *av) C_noret;
C_noret_decl(f_2353)
static void C_ccall f_2353(C_word c,C_word *av) C_noret;
C_noret_decl(f_2365)
static void C_ccall f_2365(C_word c,C_word *av) C_noret;
C_noret_decl(f_2379)
static void C_ccall f_2379(C_word c,C_word *av) C_noret;
C_noret_decl(f_2382)
static void C_ccall f_2382(C_word c,C_word *av) C_noret;
C_noret_decl(f_2385)
static void C_ccall f_2385(C_word c,C_word *av) C_noret;
C_noret_decl(f_2388)
static void C_ccall f_2388(C_word c,C_word *av) C_noret;
C_noret_decl(f_2391)
static void C_ccall f_2391(C_word c,C_word *av) C_noret;
C_noret_decl(f_2394)
static void C_ccall f_2394(C_word c,C_word *av) C_noret;
C_noret_decl(f_2397)
static void C_ccall f_2397(C_word c,C_word *av) C_noret;
C_noret_decl(f_867)
static void C_ccall f_867(C_word c,C_word *av) C_noret;
C_noret_decl(f_870)
static void C_ccall f_870(C_word c,C_word *av) C_noret;
C_noret_decl(f_873)
static void C_ccall f_873(C_word c,C_word *av) C_noret;
C_noret_decl(f_876)
static void C_ccall f_876(C_word c,C_word *av) C_noret;
C_noret_decl(f_879)
static void C_ccall f_879(C_word c,C_word *av) C_noret;
C_noret_decl(f_882)
static void C_ccall f_882(C_word c,C_word *av) C_noret;
C_noret_decl(f_889)
static void C_ccall f_889(C_word c,C_word *av) C_noret;
C_noret_decl(f_892)
static void C_ccall f_892(C_word c,C_word *av) C_noret;
C_noret_decl(f_909)
static void C_ccall f_909(C_word c,C_word *av) C_noret;
C_noret_decl(f_913)
static void C_ccall f_913(C_word c,C_word *av) C_noret;
C_noret_decl(f_916)
static void C_ccall f_916(C_word c,C_word *av) C_noret;
C_noret_decl(f_919)
static void C_ccall f_919(C_word c,C_word *av) C_noret;
C_noret_decl(f_924)
static void C_ccall f_924(C_word c,C_word *av) C_noret;
C_noret_decl(f_928)
static void C_ccall f_928(C_word c,C_word *av) C_noret;
C_noret_decl(f_931)
static void C_ccall f_931(C_word c,C_word *av) C_noret;
C_noret_decl(f_934)
static void C_ccall f_934(C_word c,C_word *av) C_noret;
C_noret_decl(f_939)
static void C_fcall f_939(C_word t0,C_word t1,C_word t2) C_noret;
C_noret_decl(f_966)
static void C_ccall f_966(C_word c,C_word *av) C_noret;
C_noret_decl(f_970)
static void C_ccall f_970(C_word c,C_word *av) C_noret;
C_noret_decl(f_973)
static void C_ccall f_973(C_word c,C_word *av) C_noret;
C_noret_decl(f_976)
static void C_ccall f_976(C_word c,C_word *av) C_noret;
C_noret_decl(C_toplevel)
C_externexport void C_ccall C_toplevel(C_word c,C_word *av) C_noret;

C_noret_decl(trf_1762)
static void C_ccall trf_1762(C_word c,C_word *av) C_noret;
static void C_ccall trf_1762(C_word c,C_word *av){
C_word t0=av[2];
C_word t1=av[1];
C_word t2=av[0];
f_1762(t0,t1,t2);}

C_noret_decl(trf_1789)
static void C_ccall trf_1789(C_word c,C_word *av) C_noret;
static void C_ccall trf_1789(C_word c,C_word *av){
C_word t0=av[2];
C_word t1=av[1];
C_word t2=av[0];
f_1789(t0,t1,t2);}

C_noret_decl(trf_1918)
static void C_ccall trf_1918(C_word c,C_word *av) C_noret;
static void C_ccall trf_1918(C_word c,C_word *av){
C_word t0=av[3];
C_word t1=av[2];
C_word t2=av[1];
C_word t3=av[0];
f_1918(t0,t1,t2,t3);}

C_noret_decl(trf_2035)
static void C_ccall trf_2035(C_word c,C_word *av) C_noret;
static void C_ccall trf_2035(C_word c,C_word *av){
C_word t0=av[2];
C_word t1=av[1];
C_word t2=av[0];
f_2035(t0,t1,t2);}

C_noret_decl(trf_2086)
static void C_ccall trf_2086(C_word c,C_word *av) C_noret;
static void C_ccall trf_2086(C_word c,C_word *av){
C_word t0=av[2];
C_word t1=av[1];
C_word t2=av[0];
f_2086(t0,t1,t2);}

C_noret_decl(trf_2114)
static void C_ccall trf_2114(C_word c,C_word *av) C_noret;
static void C_ccall trf_2114(C_word c,C_word *av){
C_word t0=av[2];
C_word t1=av[1];
C_word t2=av[0];
f_2114(t0,t1,t2);}

C_noret_decl(trf_2149)
static void C_ccall trf_2149(C_word c,C_word *av) C_noret;
static void C_ccall trf_2149(C_word c,C_word *av){
C_word t0=av[2];
C_word t1=av[1];
C_word t2=av[0];
f_2149(t0,t1,t2);}

C_noret_decl(trf_2176)
static void C_ccall trf_2176(C_word c,C_word *av) C_noret;
static void C_ccall trf_2176(C_word c,C_word *av){
C_word t0=av[2];
C_word t1=av[1];
C_word t2=av[0];
f_2176(t0,t1,t2);}

C_noret_decl(trf_2247)
static void C_ccall trf_2247(C_word c,C_word *av) C_noret;
static void C_ccall trf_2247(C_word c,C_word *av){
C_word t0=av[2];
C_word t1=av[1];
C_word t2=av[0];
f_2247(t0,t1,t2);}

C_noret_decl(trf_2269)
static void C_ccall trf_2269(C_word c,C_word *av) C_noret;
static void C_ccall trf_2269(C_word c,C_word *av){
C_word t0=av[2];
C_word t1=av[1];
C_word t2=av[0];
f_2269(t0,t1,t2);}

C_noret_decl(trf_2302)
static void C_ccall trf_2302(C_word c,C_word *av) C_noret;
static void C_ccall trf_2302(C_word c,C_word *av){
C_word t0=av[2];
C_word t1=av[1];
C_word t2=av[0];
f_2302(t0,t1,t2);}

C_noret_decl(trf_939)
static void C_ccall trf_939(C_word c,C_word *av) C_noret;
static void C_ccall trf_939(C_word c,C_word *av){
C_word t0=av[2];
C_word t1=av[1];
C_word t2=av[0];
f_939(t0,t1,t2);}

/* k1016 in k974 in k971 in k968 in crypto-ffi#ed25519-sign in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1018(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word t5;
C_word t6;
C_word t7;
C_word t8;
C_word t9;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,1)))){
C_save_and_reclaim((void *)f_1018,c,av);}
t2=(C_truep(((C_word*)t0)[2])?C_i_foreign_block_argumentp(((C_word*)t0)[2]):C_SCHEME_FALSE);
t3=(C_truep(((C_word*)t0)[3])?C_i_foreign_block_argumentp(((C_word*)t0)[3]):C_SCHEME_FALSE);
t4=(C_truep(((C_word*)t0)[4])?C_i_foreign_block_argumentp(((C_word*)t0)[4]):C_SCHEME_FALSE);
t5=C_fix((C_word)sizeof(unsigned int) * CHAR_BIT);
t6=C_i_foreign_unsigned_ranged_integer_argumentp(t1,t5);
if(C_truep(((C_word*)t0)[5])){
t7=C_i_foreign_block_argumentp(((C_word*)t0)[5]);
t8=stub66(C_SCHEME_UNDEFINED,t2,t3,t4,t6,t7);
t9=((C_word*)t0)[6];{
C_word *av2=av;
av2[0]=t9;
av2[1]=((C_word*)t0)[2];
((C_proc)(void*)(*((C_word*)t9+1)))(2,av2);}}
else{
t7=stub66(C_SCHEME_UNDEFINED,t2,t3,t4,t6,C_SCHEME_FALSE);
t8=((C_word*)t0)[6];{
C_word *av2=av;
av2[0]=t8;
av2[1]=((C_word*)t0)[2];
((C_proc)(void*)(*((C_word*)t8+1)))(2,av2);}}}

/* crypto-ffi#ed25519-verify in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1026(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2=av[2];
C_word t3=av[3];
C_word t4=av[4];
C_word t5;
C_word t6;
C_word *a;
if(c!=5) C_bad_argc_2(c,5,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(5,c,2)))){
C_save_and_reclaim((void *)f_1026,c,av);}
a=C_alloc(5);
t5=(*a=C_CLOSURE_TYPE|4,a[1]=(C_word)f_1030,a[2]=t4,a[3]=t2,a[4]=t1,tmp=(C_word)a,a+=5,tmp);
if(C_truep(C_i_stringp(t3))){
C_trace(C_text("crypto-ffi.scm:152: chicken.blob#string->blob"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[12]);
C_word *av2=av;
av2[0]=*((C_word*)lf[12]+1);
av2[1]=t5;
av2[2]=t3;
tp(3,av2);}}
else{
t6=t5;{
C_word *av2=av;
av2[0]=t6;
av2[1]=t3;
f_1030(2,av2);}}}

/* k1028 in crypto-ffi#ed25519-verify in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1030(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(6,c,2)))){
C_save_and_reclaim((void *)f_1030,c,av);}
a=C_alloc(6);
t2=(*a=C_CLOSURE_TYPE|5,a[1]=(C_word)f_1068,a[2]=((C_word*)t0)[2],a[3]=t1,a[4]=((C_word*)t0)[3],a[5]=((C_word*)t0)[4],tmp=(C_word)a,a+=6,tmp);
C_trace(C_text("crypto-ffi.scm:159: chicken.blob#blob-size"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[11]+1));
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[11]+1);
av2[1]=t2;
av2[2]=t1;
tp(3,av2);}}

/* k1066 in k1028 in crypto-ffi#ed25519-verify in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1068(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word t5;
C_word t6;
C_word t7;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,1)))){
C_save_and_reclaim((void *)f_1068,c,av);}
t2=(C_truep(((C_word*)t0)[2])?C_i_foreign_block_argumentp(((C_word*)t0)[2]):C_SCHEME_FALSE);
t3=(C_truep(((C_word*)t0)[3])?C_i_foreign_block_argumentp(((C_word*)t0)[3]):C_SCHEME_FALSE);
t4=C_fix((C_word)sizeof(unsigned int) * CHAR_BIT);
t5=C_i_foreign_unsigned_ranged_integer_argumentp(t1,t4);
if(C_truep(((C_word*)t0)[4])){
t6=C_i_foreign_block_argumentp(((C_word*)t0)[4]);
t7=((C_word*)t0)[5];{
C_word *av2=av;
av2[0]=t7;
av2[1]=C_i_nequalp(stub95(C_SCHEME_UNDEFINED,t2,t3,t5,t6),C_fix(0));
((C_proc)(void*)(*((C_word*)t7+1)))(2,av2);}}
else{
t6=((C_word*)t0)[5];{
C_word *av2=av;
av2[0]=t6;
av2[1]=C_i_nequalp(stub95(C_SCHEME_UNDEFINED,t2,t3,t5,C_SCHEME_FALSE),C_fix(0));
((C_proc)(void*)(*((C_word*)t6+1)))(2,av2);}}}

/* crypto-ffi#sha256-hash in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1076(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2=av[2];
C_word t3;
C_word t4;
C_word *a;
if(c!=3) C_bad_argc_2(c,3,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(3,c,2)))){
C_save_and_reclaim((void *)f_1076,c,av);}
a=C_alloc(3);
t3=(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1080,a[2]=t1,tmp=(C_word)a,a+=3,tmp);
if(C_truep(C_i_stringp(t2))){
C_trace(C_text("crypto-ffi.scm:168: chicken.blob#string->blob"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[12]);
C_word *av2=av;
av2[0]=*((C_word*)lf[12]+1);
av2[1]=t3;
av2[2]=t2;
tp(3,av2);}}
else{
t4=t3;{
C_word *av2=av;
av2[0]=t4;
av2[1]=t2;
f_1080(2,av2);}}}

/* k1078 in crypto-ffi#sha256-hash in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1080(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(4,c,2)))){
C_save_and_reclaim((void *)f_1080,c,av);}
a=C_alloc(4);
t2=(*a=C_CLOSURE_TYPE|3,a[1]=(C_word)f_1083,a[2]=t1,a[3]=((C_word*)t0)[2],tmp=(C_word)a,a+=4,tmp);
C_trace(C_text("crypto-ffi.scm:170: chicken.blob#make-blob"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[7]);
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[7]+1);
av2[1]=t2;
av2[2]=C_fix(32);
tp(3,av2);}}

/* k1081 in k1078 in crypto-ffi#sha256-hash in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1083(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(5,c,2)))){
C_save_and_reclaim((void *)f_1083,c,av);}
a=C_alloc(5);
t2=(*a=C_CLOSURE_TYPE|4,a[1]=(C_word)f_1111,a[2]=t1,a[3]=((C_word*)t0)[2],a[4]=((C_word*)t0)[3],tmp=(C_word)a,a+=5,tmp);
C_trace(C_text("crypto-ffi.scm:175: chicken.blob#blob-size"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[11]+1));
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[11]+1);
av2[1]=t2;
av2[2]=((C_word*)t0)[2];
tp(3,av2);}}

/* k1109 in k1081 in k1078 in crypto-ffi#sha256-hash in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1111(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word t5;
C_word t6;
C_word t7;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,1)))){
C_save_and_reclaim((void *)f_1111,c,av);}
t2=(C_truep(((C_word*)t0)[2])?C_i_foreign_block_argumentp(((C_word*)t0)[2]):C_SCHEME_FALSE);
t3=(C_truep(((C_word*)t0)[3])?C_i_foreign_block_argumentp(((C_word*)t0)[3]):C_SCHEME_FALSE);
t4=C_fix((C_word)sizeof(unsigned int) * CHAR_BIT);
t5=C_i_foreign_unsigned_ranged_integer_argumentp(t1,t4);
t6=stub117(C_SCHEME_UNDEFINED,t2,t3,t5);
t7=((C_word*)t0)[4];{
C_word *av2=av;
av2[0]=t7;
av2[1]=((C_word*)t0)[2];
((C_proc)(void*)(*((C_word*)t7+1)))(2,av2);}}

/* crypto-ffi#sha512-hash in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1119(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2=av[2];
C_word t3;
C_word t4;
C_word *a;
if(c!=3) C_bad_argc_2(c,3,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(3,c,2)))){
C_save_and_reclaim((void *)f_1119,c,av);}
a=C_alloc(3);
t3=(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1123,a[2]=t1,tmp=(C_word)a,a+=3,tmp);
if(C_truep(C_i_stringp(t2))){
C_trace(C_text("crypto-ffi.scm:183: chicken.blob#string->blob"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[12]);
C_word *av2=av;
av2[0]=*((C_word*)lf[12]+1);
av2[1]=t3;
av2[2]=t2;
tp(3,av2);}}
else{
t4=t3;{
C_word *av2=av;
av2[0]=t4;
av2[1]=t2;
f_1123(2,av2);}}}

/* k1121 in crypto-ffi#sha512-hash in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1123(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(4,c,2)))){
C_save_and_reclaim((void *)f_1123,c,av);}
a=C_alloc(4);
t2=(*a=C_CLOSURE_TYPE|3,a[1]=(C_word)f_1126,a[2]=t1,a[3]=((C_word*)t0)[2],tmp=(C_word)a,a+=4,tmp);
C_trace(C_text("crypto-ffi.scm:185: chicken.blob#make-blob"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[7]);
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[7]+1);
av2[1]=t2;
av2[2]=C_fix(64);
tp(3,av2);}}

/* k1124 in k1121 in crypto-ffi#sha512-hash in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1126(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(5,c,2)))){
C_save_and_reclaim((void *)f_1126,c,av);}
a=C_alloc(5);
t2=(*a=C_CLOSURE_TYPE|4,a[1]=(C_word)f_1154,a[2]=t1,a[3]=((C_word*)t0)[2],a[4]=((C_word*)t0)[3],tmp=(C_word)a,a+=5,tmp);
C_trace(C_text("crypto-ffi.scm:190: chicken.blob#blob-size"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[11]+1));
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[11]+1);
av2[1]=t2;
av2[2]=((C_word*)t0)[2];
tp(3,av2);}}

/* k1152 in k1124 in k1121 in crypto-ffi#sha512-hash in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1154(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word t5;
C_word t6;
C_word t7;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,1)))){
C_save_and_reclaim((void *)f_1154,c,av);}
t2=(C_truep(((C_word*)t0)[2])?C_i_foreign_block_argumentp(((C_word*)t0)[2]):C_SCHEME_FALSE);
t3=(C_truep(((C_word*)t0)[3])?C_i_foreign_block_argumentp(((C_word*)t0)[3]):C_SCHEME_FALSE);
t4=C_fix((C_word)sizeof(unsigned int) * CHAR_BIT);
t5=C_i_foreign_unsigned_ranged_integer_argumentp(t1,t4);
t6=stub137(C_SCHEME_UNDEFINED,t2,t3,t5);
t7=((C_word*)t0)[4];{
C_word *av2=av;
av2[0]=t7;
av2[1]=((C_word*)t0)[2];
((C_proc)(void*)(*((C_word*)t7+1)))(2,av2);}}

/* crypto-ffi#blake2b-hash in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1163(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2=av[2];
C_word t3;
C_word t4;
C_word *a;
if(c!=3) C_bad_argc_2(c,3,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(3,c,2)))){
C_save_and_reclaim((void *)f_1163,c,av);}
a=C_alloc(3);
t3=(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1167,a[2]=t1,tmp=(C_word)a,a+=3,tmp);
if(C_truep(C_i_stringp(t2))){
C_trace(C_text("crypto-ffi.scm:206: chicken.blob#string->blob"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[12]);
C_word *av2=av;
av2[0]=*((C_word*)lf[12]+1);
av2[1]=t3;
av2[2]=t2;
tp(3,av2);}}
else{
t4=t3;{
C_word *av2=av;
av2[0]=t4;
av2[1]=t2;
f_1167(2,av2);}}}

/* k1165 in crypto-ffi#blake2b-hash in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1167(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(4,c,2)))){
C_save_and_reclaim((void *)f_1167,c,av);}
a=C_alloc(4);
t2=(*a=C_CLOSURE_TYPE|3,a[1]=(C_word)f_1170,a[2]=t1,a[3]=((C_word*)t0)[2],tmp=(C_word)a,a+=4,tmp);
C_trace(C_text("crypto-ffi.scm:208: chicken.blob#make-blob"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[7]);
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[7]+1);
av2[1]=t2;
av2[2]=C_fast_retrieve(lf[16]);
tp(3,av2);}}

/* k1168 in k1165 in crypto-ffi#blake2b-hash in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1170(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(5,c,2)))){
C_save_and_reclaim((void *)f_1170,c,av);}
a=C_alloc(5);
t2=(*a=C_CLOSURE_TYPE|4,a[1]=(C_word)f_1215,a[2]=t1,a[3]=((C_word*)t0)[2],a[4]=((C_word*)t0)[3],tmp=(C_word)a,a+=5,tmp);
C_trace(C_text("crypto-ffi.scm:217: chicken.blob#blob-size"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[11]+1));
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[11]+1);
av2[1]=t2;
av2[2]=((C_word*)t0)[2];
tp(3,av2);}}

/* k1213 in k1168 in k1165 in crypto-ffi#blake2b-hash in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1215(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word t5;
C_word t6;
C_word t7;
C_word t8;
C_word t9;
C_word t10;
C_word t11;
C_word t12;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,1)))){
C_save_and_reclaim((void *)f_1215,c,av);}
t2=C_fast_retrieve(lf[16]);
t3=(C_truep(((C_word*)t0)[2])?C_i_foreign_block_argumentp(((C_word*)t0)[2]):C_SCHEME_FALSE);
t4=C_fix((C_word)sizeof(unsigned int) * CHAR_BIT);
t5=C_i_foreign_unsigned_ranged_integer_argumentp(C_fast_retrieve(lf[16]),t4);
t6=(C_truep(((C_word*)t0)[3])?C_i_foreign_block_argumentp(((C_word*)t0)[3]):C_SCHEME_FALSE);
t7=C_fix((C_word)sizeof(unsigned int) * CHAR_BIT);
t8=C_i_foreign_unsigned_ranged_integer_argumentp(t1,t7);
t9=C_fix((C_word)sizeof(unsigned int) * CHAR_BIT);
t10=C_i_foreign_unsigned_ranged_integer_argumentp(C_fix(0),t9);
t11=stub161(C_SCHEME_UNDEFINED,t3,t5,t6,t8,C_SCHEME_FALSE,t10);
t12=((C_word*)t0)[4];{
C_word *av2=av;
av2[0]=t12;
av2[1]=((C_word*)t0)[2];
((C_proc)(void*)(*((C_word*)t12+1)))(2,av2);}}

/* crypto-ffi#random-bytes in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1230(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2=av[2];
C_word t3;
C_word t4;
C_word *a;
if(c!=3) C_bad_argc_2(c,3,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(4,c,2)))){
C_save_and_reclaim((void *)f_1230,c,av);}
a=C_alloc(4);
t3=(*a=C_CLOSURE_TYPE|3,a[1]=(C_word)f_1234,a[2]=t2,a[3]=t1,tmp=(C_word)a,a+=4,tmp);
C_trace(C_text("crypto-ffi.scm:253: chicken.blob#make-blob"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[7]);
C_word *av2=av;
av2[0]=*((C_word*)lf[7]+1);
av2[1]=t3;
av2[2]=t2;
tp(3,av2);}}

/* k1232 in crypto-ffi#random-bytes in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1234(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word t5;
C_word t6;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,1)))){
C_save_and_reclaim((void *)f_1234,c,av);}
t2=(C_truep(t1)?C_i_foreign_block_argumentp(t1):C_SCHEME_FALSE);
t3=C_fix((C_word)sizeof(unsigned int) * CHAR_BIT);
t4=C_i_foreign_unsigned_ranged_integer_argumentp(((C_word*)t0)[2],t3);
t5=stub193(C_SCHEME_UNDEFINED,t2,t4);
t6=((C_word*)t0)[3];{
C_word *av2=av;
av2[0]=t6;
av2[1]=t1;
((C_proc)(void*)(*((C_word*)t6+1)))(2,av2);}}

/* crypto-ffi#random-u8 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1253(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
if(c!=2) C_bad_argc_2(c,2,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(3,c,2)))){
C_save_and_reclaim((void *)f_1253,c,av);}
a=C_alloc(3);
t2=(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1257,a[2]=t1,tmp=(C_word)a,a+=3,tmp);
C_trace(C_text("crypto-ffi.scm:263: chicken.blob#make-blob"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[7]);
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[7]+1);
av2[1]=t2;
av2[2]=C_fix(1);
tp(3,av2);}}

/* k1255 in crypto-ffi#random-u8 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1257(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word t5;
C_word t6;
C_word t7;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(4,c,2)))){
C_save_and_reclaim((void *)f_1257,c,av);}
a=C_alloc(4);
t2=(C_truep(t1)?C_i_foreign_block_argumentp(t1):C_SCHEME_FALSE);
t3=C_fix((C_word)sizeof(unsigned int) * CHAR_BIT);
t4=C_i_foreign_unsigned_ranged_integer_argumentp(C_fix(1),t3);
t5=stub207(C_SCHEME_UNDEFINED,t2,t4);
t6=(*a=C_CLOSURE_TYPE|3,a[1]=(C_word)f_1277,a[2]=((C_word*)t0)[2],a[3]=t1,tmp=(C_word)a,a+=4,tmp);
C_trace(C_text("crypto-ffi.scm:268: srfi-4#blob->u8vector/shared"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[9]+1));
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[9]+1);
av2[1]=t6;
av2[2]=t1;
tp(3,av2);}}

/* k1275 in k1255 in crypto-ffi#random-u8 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1277(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(3,c,2)))){
C_save_and_reclaim((void *)f_1277,c,av);}
a=C_alloc(3);
t2=(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1284,a[2]=((C_word*)t0)[2],tmp=(C_word)a,a+=3,tmp);
C_trace(C_text("crypto-ffi.scm:269: srfi-4#blob->u8vector/shared"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[9]+1));
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[9]+1);
av2[1]=t2;
av2[2]=((C_word*)t0)[3];
tp(3,av2);}}

/* k1282 in k1275 in k1255 in crypto-ffi#random-u8 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1284(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,1)))){
C_save_and_reclaim((void *)f_1284,c,av);}
t2=((C_word*)t0)[2];{
C_word *av2=av;
av2[0]=t2;
av2[1]=C_i_u8vector_ref(t1,C_fix(0));
((C_proc)(void*)(*((C_word*)t2+1)))(2,av2);}}

/* crypto-ffi#random-u32 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1286(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word *a;
if(c!=2) C_bad_argc_2(c,2,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,1)))){
C_save_and_reclaim((void *)f_1286,c,av);}
t2=t1;{
C_word *av2=av;
av2[0]=t2;
av2[1]=stub219(C_SCHEME_UNDEFINED);
((C_proc)(void*)(*((C_word*)t2+1)))(2,av2);}}

/* crypto-ffi#random-uniform in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1294(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2=av[2];
C_word t3;
C_word *a;
if(c!=3) C_bad_argc_2(c,3,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,1)))){
C_save_and_reclaim((void *)f_1294,c,av);}
t3=t1;{
C_word *av2=av;
av2[0]=t3;
av2[1]=stub226(C_SCHEME_UNDEFINED,C_i_foreign_fixnum_argumentp(t2));
((C_proc)(void*)(*((C_word*)t3+1)))(2,av2);}}

/* crypto-ffi#entropy-status in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1306(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word *a;
if(c!=2) C_bad_argc_2(c,2,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(8,c,3)))){
C_save_and_reclaim((void *)f_1306,c,av);}
a=C_alloc(8);
t2=(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1316,a[2]=t1,tmp=(C_word)a,a+=3,tmp);
t3=C_a_i_bytevector(&a,1,C_fix(3));
C_trace(C_text("crypto-ffi.scm:287: ##sys#peek-c-string"));
t4=*((C_word*)lf[36]+1);{
C_word *av2;
if(c >= 4) {
  av2=av;
} else {
  av2=C_alloc(4);
}
av2[0]=t4;
av2[1]=t2;
av2[2]=stub233(t3);
av2[3]=C_fix(0);
((C_proc)(void*)(*((C_word*)t4+1)))(4,av2);}}

/* k1314 in crypto-ffi#entropy-status in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1316(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word t5;
C_word t6;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(18,c,1)))){
C_save_and_reclaim((void *)f_1316,c,av);}
a=C_alloc(18);
t2=C_a_i_cons(&a,2,lf[27],t1);
if(C_truep(C_i_string_equal_p(t1,lf[28]))){
t3=C_a_i_cons(&a,2,lf[29],lf[30]);
t4=C_a_i_cons(&a,2,lf[31],lf[32]);
t5=((C_word*)t0)[2];{
C_word *av2=av;
av2[0]=t5;
av2[1]=C_a_i_list(&a,3,t2,t3,t4);
((C_proc)(void*)(*((C_word*)t5+1)))(2,av2);}}
else{
t3=C_i_string_equal_p(t1,lf[33]);
t4=(C_truep(t3)?C_a_i_cons(&a,2,lf[29],lf[34]):C_a_i_cons(&a,2,lf[29],lf[35]));
t5=C_a_i_cons(&a,2,lf[31],lf[32]);
t6=((C_word*)t0)[2];{
C_word *av2=av;
av2[0]=t6;
av2[1]=C_a_i_list(&a,3,t2,t4,t5);
((C_proc)(void*)(*((C_word*)t6+1)))(2,av2);}}}

/* crypto-ffi#memzero! in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1346(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2=av[2];
C_word t3;
C_word t4;
C_word *a;
if(c!=3) C_bad_argc_2(c,3,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(4,c,2)))){
C_save_and_reclaim((void *)f_1346,c,av);}
a=C_alloc(4);
t3=(*a=C_CLOSURE_TYPE|3,a[1]=(C_word)f_1368,a[2]=t2,a[3]=t1,tmp=(C_word)a,a+=4,tmp);
C_trace(C_text("crypto-ffi.scm:301: chicken.blob#blob-size"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[11]+1));
C_word *av2=av;
av2[0]=*((C_word*)lf[11]+1);
av2[1]=t3;
av2[2]=t2;
tp(3,av2);}}

/* k1366 in crypto-ffi#memzero! in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1368(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,1)))){
C_save_and_reclaim((void *)f_1368,c,av);}
t2=(C_truep(((C_word*)t0)[2])?C_i_foreign_block_argumentp(((C_word*)t0)[2]):C_SCHEME_FALSE);
t3=C_fix((C_word)sizeof(unsigned int) * CHAR_BIT);
t4=((C_word*)t0)[3];{
C_word *av2=av;
av2[0]=t4;
av2[1]=stub249(C_SCHEME_UNDEFINED,t2,C_i_foreign_unsigned_ranged_integer_argumentp(t1,t3));
((C_proc)(void*)(*((C_word*)t4+1)))(2,av2);}}

/* crypto-ffi#argon2id-hash in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1370(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2=av[2];
C_word t3=av[3];
C_word t4;
C_word t5;
C_word *a;
if(c!=4) C_bad_argc_2(c,4,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(4,c,2)))){
C_save_and_reclaim((void *)f_1370,c,av);}
a=C_alloc(4);
t4=(*a=C_CLOSURE_TYPE|3,a[1]=(C_word)f_1374,a[2]=t3,a[3]=t1,tmp=(C_word)a,a+=4,tmp);
if(C_truep(C_i_stringp(t2))){
C_trace(C_text("crypto-ffi.scm:309: chicken.blob#string->blob"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[12]);
C_word *av2=av;
av2[0]=*((C_word*)lf[12]+1);
av2[1]=t4;
av2[2]=t2;
tp(3,av2);}}
else{
t5=t4;{
C_word *av2=av;
av2[0]=t5;
av2[1]=t2;
f_1374(2,av2);}}}

/* k1372 in crypto-ffi#argon2id-hash in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1374(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(5,c,2)))){
C_save_and_reclaim((void *)f_1374,c,av);}
a=C_alloc(5);
t2=(*a=C_CLOSURE_TYPE|4,a[1]=(C_word)f_1377,a[2]=t1,a[3]=((C_word*)t0)[2],a[4]=((C_word*)t0)[3],tmp=(C_word)a,a+=5,tmp);
C_trace(C_text("crypto-ffi.scm:311: chicken.blob#make-blob"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[7]);
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[7]+1);
av2[1]=t2;
av2[2]=C_fast_retrieve(lf[18]);
tp(3,av2);}}

/* k1375 in k1372 in crypto-ffi#argon2id-hash in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1377(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(6,c,2)))){
C_save_and_reclaim((void *)f_1377,c,av);}
a=C_alloc(6);
t2=(*a=C_CLOSURE_TYPE|5,a[1]=(C_word)f_1440,a[2]=t1,a[3]=((C_word*)t0)[2],a[4]=((C_word*)t0)[3],a[5]=((C_word*)t0)[4],tmp=(C_word)a,a+=6,tmp);
C_trace(C_text("crypto-ffi.scm:323: chicken.blob#blob-size"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[11]+1));
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[11]+1);
av2[1]=t2;
av2[2]=((C_word*)t0)[2];
tp(3,av2);}}

/* k1438 in k1375 in k1372 in crypto-ffi#argon2id-hash in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1440(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word t5;
C_word t6;
C_word t7;
C_word t8;
C_word t9;
C_word t10;
C_word t11;
C_word t12;
C_word t13;
C_word t14;
C_word t15;
C_word t16;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,2)))){
C_save_and_reclaim((void *)f_1440,c,av);}
t2=C_fast_retrieve(lf[18]);
t3=(C_truep(((C_word*)t0)[2])?C_i_foreign_block_argumentp(((C_word*)t0)[2]):C_SCHEME_FALSE);
t4=C_fix((C_word)sizeof(unsigned int) * CHAR_BIT);
t5=C_i_foreign_unsigned_ranged_integer_argumentp(C_fast_retrieve(lf[18]),t4);
t6=(C_truep(((C_word*)t0)[3])?C_i_foreign_block_argumentp(((C_word*)t0)[3]):C_SCHEME_FALSE);
t7=C_fix((C_word)sizeof(unsigned int) * CHAR_BIT);
t8=C_i_foreign_unsigned_ranged_integer_argumentp(t1,t7);
t9=(C_truep(((C_word*)t0)[4])?C_i_foreign_block_argumentp(((C_word*)t0)[4]):C_SCHEME_FALSE);
t10=C_fix((C_word)sizeof(unsigned int) * CHAR_BIT);
t11=C_i_foreign_unsigned_ranged_integer_argumentp(C_fix(3),t10);
t12=C_fix((C_word)sizeof(unsigned int) * CHAR_BIT);
t13=C_i_foreign_unsigned_ranged_integer_argumentp(C_fix(268435456),t12);
t14=C_fix(2);
t15=stub272(C_SCHEME_UNDEFINED,t3,t5,t6,t8,t9,t11,t13,t14);
if(C_truep(C_i_nequalp(t15,C_fix(0)))){
t16=((C_word*)t0)[5];{
C_word *av2=av;
av2[0]=t16;
av2[1]=((C_word*)t0)[2];
((C_proc)(void*)(*((C_word*)t16+1)))(2,av2);}}
else{
C_trace(C_text("crypto-ffi.scm:330: chicken.base#error"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[39]+1));
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[39]+1);
av2[1]=((C_word*)t0)[5];
av2[2]=lf[40];
tp(3,av2);}}}

/* crypto-ffi#secretbox-encrypt in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1448(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2=av[2];
C_word t3=av[3];
C_word t4=av[4];
C_word t5;
C_word t6;
C_word *a;
if(c!=5) C_bad_argc_2(c,5,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(6,c,2)))){
C_save_and_reclaim((void *)f_1448,c,av);}
a=C_alloc(6);
t5=(*a=C_CLOSURE_TYPE|5,a[1]=(C_word)f_1452,a[2]=t2,a[3]=t3,a[4]=t4,a[5]=t1,tmp=(C_word)a,a+=6,tmp);
C_trace(C_text("crypto-ffi.scm:338: chicken.blob#blob-size"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[11]+1));
C_word *av2=av;
av2[0]=*((C_word*)lf[11]+1);
av2[1]=t5;
av2[2]=t2;
tp(3,av2);}}

/* k1450 in crypto-ffi#secretbox-encrypt in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1452(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(36,c,2)))){
C_save_and_reclaim((void *)f_1452,c,av);}
a=C_alloc(36);
t2=(*a=C_CLOSURE_TYPE|6,a[1]=(C_word)f_1455,a[2]=((C_word*)t0)[2],a[3]=t1,a[4]=((C_word*)t0)[3],a[5]=((C_word*)t0)[4],a[6]=((C_word*)t0)[5],tmp=(C_word)a,a+=7,tmp);
t3=C_s_a_i_plus(&a,2,t1,C_fix(16));
C_trace(C_text("crypto-ffi.scm:339: chicken.blob#make-blob"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[7]);
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[7]+1);
av2[1]=t2;
av2[2]=t3;
tp(3,av2);}}

/* k1453 in k1450 in crypto-ffi#secretbox-encrypt in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1455(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word t5;
C_word t6;
C_word t7;
C_word t8;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,2)))){
C_save_and_reclaim((void *)f_1455,c,av);}
t2=(C_truep(t1)?C_i_foreign_block_argumentp(t1):C_SCHEME_FALSE);
t3=(C_truep(((C_word*)t0)[2])?C_i_foreign_block_argumentp(((C_word*)t0)[2]):C_SCHEME_FALSE);
t4=C_fix((C_word)sizeof(unsigned int) * CHAR_BIT);
t5=C_i_foreign_unsigned_ranged_integer_argumentp(((C_word*)t0)[3],t4);
t6=(C_truep(((C_word*)t0)[4])?C_i_foreign_block_argumentp(((C_word*)t0)[4]):C_SCHEME_FALSE);
t7=(C_truep(((C_word*)t0)[5])?stub306(C_SCHEME_UNDEFINED,t2,t3,t5,t6,C_i_foreign_block_argumentp(((C_word*)t0)[5])):stub306(C_SCHEME_UNDEFINED,t2,t3,t5,t6,C_SCHEME_FALSE));
if(C_truep(C_i_nequalp(t7,C_fix(0)))){
t8=((C_word*)t0)[6];{
C_word *av2=av;
av2[0]=t8;
av2[1]=t1;
((C_proc)(void*)(*((C_word*)t8+1)))(2,av2);}}
else{
C_trace(C_text("crypto-ffi.scm:350: chicken.base#error"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[39]+1));
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[39]+1);
av2[1]=((C_word*)t0)[6];
av2[2]=lf[42];
tp(3,av2);}}}

/* crypto-ffi#secretbox-decrypt in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1508(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2=av[2];
C_word t3=av[3];
C_word t4=av[4];
C_word t5;
C_word t6;
C_word *a;
if(c!=5) C_bad_argc_2(c,5,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(6,c,2)))){
C_save_and_reclaim((void *)f_1508,c,av);}
a=C_alloc(6);
t5=(*a=C_CLOSURE_TYPE|5,a[1]=(C_word)f_1512,a[2]=t2,a[3]=t3,a[4]=t4,a[5]=t1,tmp=(C_word)a,a+=6,tmp);
C_trace(C_text("crypto-ffi.scm:358: chicken.blob#blob-size"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[11]+1));
C_word *av2=av;
av2[0]=*((C_word*)lf[11]+1);
av2[1]=t5;
av2[2]=t2;
tp(3,av2);}}

/* k1510 in crypto-ffi#secretbox-decrypt in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1512(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(36,c,2)))){
C_save_and_reclaim((void *)f_1512,c,av);}
a=C_alloc(36);
t2=(*a=C_CLOSURE_TYPE|6,a[1]=(C_word)f_1515,a[2]=((C_word*)t0)[2],a[3]=t1,a[4]=((C_word*)t0)[3],a[5]=((C_word*)t0)[4],a[6]=((C_word*)t0)[5],tmp=(C_word)a,a+=7,tmp);
t3=C_s_a_i_minus(&a,2,t1,C_fix(16));
C_trace(C_text("crypto-ffi.scm:359: chicken.blob#make-blob"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[7]);
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[7]+1);
av2[1]=t2;
av2[2]=t3;
tp(3,av2);}}

/* k1513 in k1510 in crypto-ffi#secretbox-decrypt in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1515(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word t5;
C_word t6;
C_word t7;
C_word t8;
C_word t9;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,1)))){
C_save_and_reclaim((void *)f_1515,c,av);}
t2=(C_truep(t1)?C_i_foreign_block_argumentp(t1):C_SCHEME_FALSE);
t3=(C_truep(((C_word*)t0)[2])?C_i_foreign_block_argumentp(((C_word*)t0)[2]):C_SCHEME_FALSE);
t4=C_fix((C_word)sizeof(unsigned int) * CHAR_BIT);
t5=C_i_foreign_unsigned_ranged_integer_argumentp(((C_word*)t0)[3],t4);
t6=(C_truep(((C_word*)t0)[4])?C_i_foreign_block_argumentp(((C_word*)t0)[4]):C_SCHEME_FALSE);
t7=(C_truep(((C_word*)t0)[5])?stub336(C_SCHEME_UNDEFINED,t2,t3,t5,t6,C_i_foreign_block_argumentp(((C_word*)t0)[5])):stub336(C_SCHEME_UNDEFINED,t2,t3,t5,t6,C_SCHEME_FALSE));
t8=C_i_nequalp(t7,C_fix(0));
t9=((C_word*)t0)[6];{
C_word *av2=av;
av2[0]=t9;
av2[1]=(C_truep(t8)?t1:C_SCHEME_FALSE);
((C_proc)(void*)(*((C_word*)t9+1)))(2,av2);}}

/* crypto-ffi#x25519-keypair in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1577(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
if(c!=2) C_bad_argc_2(c,2,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(3,c,2)))){
C_save_and_reclaim((void *)f_1577,c,av);}
a=C_alloc(3);
t2=(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1581,a[2]=t1,tmp=(C_word)a,a+=3,tmp);
C_trace(C_text("crypto-ffi.scm:411: chicken.blob#make-blob"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[7]);
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[7]+1);
av2[1]=t2;
av2[2]=C_fast_retrieve(lf[20]);
tp(3,av2);}}

/* k1579 in crypto-ffi#x25519-keypair in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1581(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(4,c,2)))){
C_save_and_reclaim((void *)f_1581,c,av);}
a=C_alloc(4);
t2=(*a=C_CLOSURE_TYPE|3,a[1]=(C_word)f_1584,a[2]=t1,a[3]=((C_word*)t0)[2],tmp=(C_word)a,a+=4,tmp);
C_trace(C_text("crypto-ffi.scm:412: chicken.blob#make-blob"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[7]);
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[7]+1);
av2[1]=t2;
av2[2]=C_fast_retrieve(lf[21]);
tp(3,av2);}}

/* k1582 in k1579 in crypto-ffi#x25519-keypair in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1584(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word t5;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(6,c,1)))){
C_save_and_reclaim((void *)f_1584,c,av);}
a=C_alloc(6);
t2=(C_truep(((C_word*)t0)[2])?C_i_foreign_block_argumentp(((C_word*)t0)[2]):C_SCHEME_FALSE);
if(C_truep(t1)){
t3=C_i_foreign_block_argumentp(t1);
t4=stub371(C_SCHEME_UNDEFINED,t2,t3);
t5=((C_word*)t0)[3];{
C_word *av2=av;
av2[0]=t5;
av2[1]=C_a_i_list2(&a,2,((C_word*)t0)[2],t1);
((C_proc)(void*)(*((C_word*)t5+1)))(2,av2);}}
else{
t3=stub371(C_SCHEME_UNDEFINED,t2,C_SCHEME_FALSE);
t4=((C_word*)t0)[3];{
C_word *av2=av;
av2[0]=t4;
av2[1]=C_a_i_list2(&a,2,((C_word*)t0)[2],t1);
((C_proc)(void*)(*((C_word*)t4+1)))(2,av2);}}}

/* crypto-ffi#x25519-scalarmult in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1608(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2=av[2];
C_word t3=av[3];
C_word t4;
C_word t5;
C_word *a;
if(c!=4) C_bad_argc_2(c,4,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(5,c,2)))){
C_save_and_reclaim((void *)f_1608,c,av);}
a=C_alloc(5);
t4=(*a=C_CLOSURE_TYPE|4,a[1]=(C_word)f_1612,a[2]=t2,a[3]=t3,a[4]=t1,tmp=(C_word)a,a+=5,tmp);
C_trace(C_text("crypto-ffi.scm:424: chicken.blob#make-blob"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[7]);
C_word *av2=av;
av2[0]=*((C_word*)lf[7]+1);
av2[1]=t4;
av2[2]=C_fix(32);
tp(3,av2);}}

/* k1610 in crypto-ffi#x25519-scalarmult in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1612(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word t5;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,2)))){
C_save_and_reclaim((void *)f_1612,c,av);}
t2=(C_truep(t1)?C_i_foreign_block_argumentp(t1):C_SCHEME_FALSE);
t3=(C_truep(((C_word*)t0)[2])?C_i_foreign_block_argumentp(((C_word*)t0)[2]):C_SCHEME_FALSE);
t4=(C_truep(((C_word*)t0)[3])?stub390(C_SCHEME_UNDEFINED,t2,t3,C_i_foreign_block_argumentp(((C_word*)t0)[3])):stub390(C_SCHEME_UNDEFINED,t2,t3,C_SCHEME_FALSE));
if(C_truep(C_i_nequalp(t4,C_fix(0)))){
t5=((C_word*)t0)[4];{
C_word *av2=av;
av2[0]=t5;
av2[1]=t1;
((C_proc)(void*)(*((C_word*)t5+1)))(2,av2);}}
else{
C_trace(C_text("crypto-ffi.scm:433: chicken.base#error"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[39]+1));
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[39]+1);
av2[1]=((C_word*)t0)[4];
av2[2]=lf[58];
tp(3,av2);}}}

/* k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1747(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(3,c,2)))){
C_save_and_reclaim((void *)f_1747,c,av);}
a=C_alloc(3);
t2=C_mutate(&lf[59] /* (set! crypto-ffi#gf256-exp ...) */,t1);
t3=(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1751,a[2]=((C_word*)t0)[2],tmp=(C_word)a,a+=3,tmp);
C_trace(C_text("crypto-ffi.scm:464: srfi-4#make-u8vector"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[82]);
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[82]+1);
av2[1]=t3;
av2[2]=C_fix(256);
tp(3,av2);}}

/* k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1751(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word t5;
C_word t6;
C_word t7;
C_word t8;
C_word t9;
C_word t10;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(15,c,3)))){
C_save_and_reclaim((void *)f_1751,c,av);}
a=C_alloc(15);
t2=C_mutate(&lf[60] /* (set! crypto-ffi#gf256-log ...) */,t1);
t3=(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1834,a[2]=((C_word*)t0)[2],tmp=(C_word)a,a+=3,tmp);
t4=C_fix(1);
t5=(*a=C_VECTOR_TYPE|1,a[1]=t4,tmp=(C_word)a,a+=2,tmp);
t6=(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1757,a[2]=t3,tmp=(C_word)a,a+=3,tmp);
t7=C_SCHEME_UNDEFINED;
t8=(*a=C_VECTOR_TYPE|1,a[1]=t7,tmp=(C_word)a,a+=2,tmp);
t9=C_set_block_item(t8,0,(*a=C_CLOSURE_TYPE|4,a[1]=(C_word)f_1789,a[2]=t5,a[3]=t8,a[4]=((C_word)li43),tmp=(C_word)a,a+=5,tmp));
t10=((C_word*)t8)[1];
f_1789(t10,t6,C_fix(0));}

/* k1755 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1757(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word t5;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(6,c,3)))){
C_save_and_reclaim((void *)f_1757,c,av);}
a=C_alloc(6);
t2=C_SCHEME_UNDEFINED;
t3=(*a=C_VECTOR_TYPE|1,a[1]=t2,tmp=(C_word)a,a+=2,tmp);
t4=C_set_block_item(t3,0,(*a=C_CLOSURE_TYPE|3,a[1]=(C_word)f_1762,a[2]=t3,a[3]=((C_word)li42),tmp=(C_word)a,a+=4,tmp));
t5=((C_word*)t3)[1];
f_1762(t5,((C_word*)t0)[2],C_fix(255));}

/* doloop430 in k1755 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_fcall f_1762(C_word t0,C_word t1,C_word t2){
C_word tmp;
C_word t3;
C_word t4;
C_word t5;
C_word t6;
C_word t7;
C_word t8;
C_word t9;
C_word *a;
loop:
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(58,0,2)))){
C_save_and_reclaim_args((void *)trf_1762,3,t0,t1,t2);}
a=C_alloc(58);
if(C_truep(C_i_nequalp(t2,C_fix(510)))){
t3=C_SCHEME_UNDEFINED;
t4=t1;{
C_word av2[2];
av2[0]=t4;
av2[1]=t3;
((C_proc)(void*)(*((C_word*)t4+1)))(2,av2);}}
else{
t3=C_s_a_i_minus(&a,2,t2,C_fix(255));
t4=C_i_u8vector_ref(C_retrieve2(lf[59],C_text("crypto-ffi#gf256-exp")),t3);
t5=C_i_u8vector_set(C_retrieve2(lf[59],C_text("crypto-ffi#gf256-exp")),t2,t4);
t6=C_s_a_i_plus(&a,2,t2,C_fix(1));
t8=t1;
t9=t6;
t1=t8;
t2=t9;
goto loop;}}

/* doloop432 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_fcall f_1789(C_word t0,C_word t1,C_word t2){
C_word tmp;
C_word t3;
C_word t4;
C_word t5;
C_word t6;
C_word t7;
C_word t8;
C_word t9;
C_word t10;
C_word t11;
C_word t12;
C_word t13;
C_word *a;
loop:
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(44,0,2)))){
C_save_and_reclaim_args((void *)trf_1789,3,t0,t1,t2);}
a=C_alloc(44);
if(C_truep(C_i_nequalp(t2,C_fix(255)))){
t3=C_SCHEME_UNDEFINED;
t4=t1;{
C_word av2[2];
av2[0]=t4;
av2[1]=t3;
((C_proc)(void*)(*((C_word*)t4+1)))(2,av2);}}
else{
t3=C_i_u8vector_set(C_retrieve2(lf[59],C_text("crypto-ffi#gf256-exp")),t2,((C_word*)((C_word*)t0)[2])[1]);
t4=C_i_u8vector_set(C_retrieve2(lf[60],C_text("crypto-ffi#gf256-log")),((C_word*)((C_word*)t0)[2])[1],t2);
if(C_truep(C_i_lessp(t2,C_fix(254)))){
t5=C_s_a_i_arithmetic_shift(&a,2,((C_word*)((C_word*)t0)[2])[1],C_fix(1));
t6=C_i_greater_or_equalp(t5,C_fix(256));
t7=(C_truep(t6)?C_s_a_i_bitwise_xor(&a,2,t5,C_fix(283)):t5);
t8=C_s_a_i_bitwise_xor(&a,2,t7,((C_word*)((C_word*)t0)[2])[1]);
t9=C_mutate(((C_word *)((C_word*)t0)[2])+1,t8);
t10=C_s_a_i_plus(&a,2,t2,C_fix(1));
t12=t1;
t13=t10;
t1=t12;
t2=t13;
goto loop;}
else{
t5=C_s_a_i_plus(&a,2,t2,C_fix(1));
t12=t1;
t13=t5;
t1=t12;
t2=t13;
goto loop;}}}

/* k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1834(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word t5;
C_word t6;
C_word t7;
C_word t8;
C_word t9;
C_word t10;
C_word t11;
C_word t12;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(30,c,4)))){
C_save_and_reclaim((void *)f_1834,c,av);}
a=C_alloc(30);
t2=C_mutate((C_word*)lf[61]+1 /* (set! crypto-ffi#gf256-add ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1836,a[2]=((C_word)li21),tmp=(C_word)a,a+=3,tmp));
t3=C_mutate((C_word*)lf[62]+1 /* (set! crypto-ffi#gf256-mul ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1842,a[2]=((C_word)li22),tmp=(C_word)a,a+=3,tmp));
t4=C_mutate((C_word*)lf[63]+1 /* (set! crypto-ffi#gf256-div ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1876,a[2]=((C_word)li23),tmp=(C_word)a,a+=3,tmp));
t5=C_mutate((C_word*)lf[64]+1 /* (set! crypto-ffi#shamir-share? ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1957,a[2]=((C_word)li24),tmp=(C_word)a,a+=3,tmp));
t6=C_mutate((C_word*)lf[66]+1 /* (set! crypto-ffi#share-id ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1963,a[2]=((C_word)li25),tmp=(C_word)a,a+=3,tmp));
t7=C_mutate((C_word*)lf[68]+1 /* (set! crypto-ffi#share-threshold ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1972,a[2]=((C_word)li26),tmp=(C_word)a,a+=3,tmp));
t8=C_mutate((C_word*)lf[70]+1 /* (set! crypto-ffi#share-x ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1981,a[2]=((C_word)li27),tmp=(C_word)a,a+=3,tmp));
t9=C_mutate((C_word*)lf[72]+1 /* (set! crypto-ffi#share-y ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1990,a[2]=((C_word)li28),tmp=(C_word)a,a+=3,tmp));
t10=C_mutate((C_word*)lf[74]+1 /* (set! crypto-ffi#shamir-split ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1999,a[2]=((C_word)li37),tmp=(C_word)a,a+=3,tmp));
t11=C_mutate((C_word*)lf[89]+1 /* (set! crypto-ffi#shamir-reconstruct ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_2217,a[2]=((C_word)li41),tmp=(C_word)a,a+=3,tmp));
t12=((C_word*)t0)[2];{
C_word *av2=av;
av2[0]=t12;
av2[1]=C_SCHEME_UNDEFINED;
((C_proc)(void*)(*((C_word*)t12+1)))(2,av2);}}

/* crypto-ffi#gf256-add in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1836(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2=av[2];
C_word t3=av[3];
C_word t4;
C_word *a;
if(c!=4) C_bad_argc_2(c,4,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(5,c,1)))){
C_save_and_reclaim((void *)f_1836,c,av);}
a=C_alloc(5);
t4=t1;{
C_word *av2=av;
av2[0]=t4;
av2[1]=C_s_a_i_bitwise_xor(&a,2,t2,t3);
((C_proc)(void*)(*((C_word*)t4+1)))(2,av2);}}

/* crypto-ffi#gf256-mul in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1842(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2=av[2];
C_word t3=av[3];
C_word t4;
C_word t5;
C_word t6;
C_word t7;
C_word t8;
C_word t9;
C_word t10;
C_word *a;
if(c!=4) C_bad_argc_2(c,4,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(34,c,1)))){
C_save_and_reclaim((void *)f_1842,c,av);}
a=C_alloc(34);
t4=C_i_nequalp(t2,C_fix(0));
t5=(C_truep(t4)?t4:C_i_nequalp(t3,C_fix(0)));
if(C_truep(t5)){
t6=t1;{
C_word *av2=av;
av2[0]=t6;
av2[1]=C_fix(0);
((C_proc)(void*)(*((C_word*)t6+1)))(2,av2);}}
else{
t6=C_i_u8vector_ref(C_retrieve2(lf[60],C_text("crypto-ffi#gf256-log")),t2);
t7=C_i_u8vector_ref(C_retrieve2(lf[60],C_text("crypto-ffi#gf256-log")),t3);
t8=C_s_a_i_plus(&a,2,t6,t7);
t9=C_s_a_i_modulo(&a,2,t8,C_fix(255));
t10=t1;{
C_word *av2=av;
av2[0]=t10;
av2[1]=C_i_u8vector_ref(C_retrieve2(lf[59],C_text("crypto-ffi#gf256-exp")),t9);
((C_proc)(void*)(*((C_word*)t10+1)))(2,av2);}}}

/* crypto-ffi#gf256-div in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1876(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2=av[2];
C_word t3=av[3];
C_word t4;
C_word t5;
C_word t6;
C_word t7;
C_word t8;
C_word t9;
C_word *a;
if(c!=4) C_bad_argc_2(c,4,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(63,c,1)))){
C_save_and_reclaim((void *)f_1876,c,av);}
a=C_alloc(63);
if(C_truep(C_i_nequalp(t2,C_fix(0)))){
t4=t1;{
C_word *av2=av;
av2[0]=t4;
av2[1]=C_fix(0);
((C_proc)(void*)(*((C_word*)t4+1)))(2,av2);}}
else{
t4=C_i_u8vector_ref(C_retrieve2(lf[60],C_text("crypto-ffi#gf256-log")),t2);
t5=C_s_a_i_plus(&a,2,t4,C_fix(255));
t6=C_i_u8vector_ref(C_retrieve2(lf[60],C_text("crypto-ffi#gf256-log")),t3);
t7=C_s_a_i_minus(&a,2,t5,t6);
t8=C_s_a_i_modulo(&a,2,t7,C_fix(255));
t9=t1;{
C_word *av2=av;
av2[0]=t9;
av2[1]=C_i_u8vector_ref(C_retrieve2(lf[59],C_text("crypto-ffi#gf256-exp")),t8);
((C_proc)(void*)(*((C_word*)t9+1)))(2,av2);}}}

/* loop in k2141 in doloop517 in k2100 in k2094 in doloop507 in k2022 in k2019 in k2013 in k2010 in k2007 in k2004 in k2001 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in ... */
static void C_fcall f_1918(C_word t0,C_word t1,C_word t2,C_word t3){
C_word tmp;
C_word t4;
C_word t5;
C_word t6;
C_word t7;
C_word t8;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(38,0,3)))){
C_save_and_reclaim_args((void *)trf_1918,4,t0,t1,t2,t3);}
a=C_alloc(38);
if(C_truep(C_i_lessp(t2,C_fix(0)))){
t4=t1;{
C_word av2[2];
av2[0]=t4;
av2[1]=t3;
((C_proc)(void*)(*((C_word*)t4+1)))(2,av2);}}
else{
t4=C_s_a_i_minus(&a,2,t2,C_fix(1));
t5=(*a=C_CLOSURE_TYPE|4,a[1]=(C_word)f_1936,a[2]=((C_word*)t0)[2],a[3]=t1,a[4]=t4,tmp=(C_word)a,a+=5,tmp);
t6=C_i_list_ref(((C_word*)t0)[3],t2);
t7=(*a=C_CLOSURE_TYPE|3,a[1]=(C_word)f_1944,a[2]=t5,a[3]=t6,tmp=(C_word)a,a+=4,tmp);
C_trace(C_text("crypto-ffi.scm:522: gf256-mul"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[62]);
C_word av2[4];
av2[0]=*((C_word*)lf[62]+1);
av2[1]=t7;
av2[2]=t3;
av2[3]=((C_word*)t0)[4];
tp(4,av2);}}}

/* k1934 in loop in k2141 in doloop517 in k2100 in k2094 in doloop507 in k2022 in k2019 in k2013 in k2010 in k2007 in k2004 in k2001 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in ... */
static void C_ccall f_1936(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,3)))){
C_save_and_reclaim((void *)f_1936,c,av);}
C_trace(C_text("crypto-ffi.scm:520: loop"));
t2=((C_word*)((C_word*)t0)[2])[1];
f_1918(t2,((C_word*)t0)[3],((C_word*)t0)[4],t1);}

/* k1942 in loop in k2141 in doloop517 in k2100 in k2094 in doloop507 in k2022 in k2019 in k2013 in k2010 in k2007 in k2004 in k2001 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in ... */
static void C_ccall f_1944(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,3)))){
C_save_and_reclaim((void *)f_1944,c,av);}
C_trace(C_text("crypto-ffi.scm:521: gf256-add"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[61]);
C_word *av2;
if(c >= 4) {
  av2=av;
} else {
  av2=C_alloc(4);
}
av2[0]=*((C_word*)lf[61]+1);
av2[1]=((C_word*)t0)[2];
av2[2]=((C_word*)t0)[3];
av2[3]=t1;
tp(4,av2);}}

/* crypto-ffi#shamir-share? in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1957(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2=av[2];
C_word t3;
C_word *a;
if(c!=3) C_bad_argc_2(c,3,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,1)))){
C_save_and_reclaim((void *)f_1957,c,av);}
t3=t1;{
C_word *av2=av;
av2[0]=t3;
av2[1]=C_i_structurep(t2,lf[65]);
((C_proc)(void*)(*((C_word*)t3+1)))(2,av2);}}

/* crypto-ffi#share-id in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1963(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2=av[2];
C_word t3;
C_word t4;
C_word *a;
if(c!=3) C_bad_argc_2(c,3,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,1)))){
C_save_and_reclaim((void *)f_1963,c,av);}
t3=C_i_check_structure_2(t2,lf[65],lf[67]);
t4=t1;{
C_word *av2=av;
av2[0]=t4;
av2[1]=C_i_block_ref(t2,C_fix(1));
((C_proc)(void*)(*((C_word*)t4+1)))(2,av2);}}

/* crypto-ffi#share-threshold in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1972(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2=av[2];
C_word t3;
C_word t4;
C_word *a;
if(c!=3) C_bad_argc_2(c,3,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,1)))){
C_save_and_reclaim((void *)f_1972,c,av);}
t3=C_i_check_structure_2(t2,lf[65],lf[69]);
t4=t1;{
C_word *av2=av;
av2[0]=t4;
av2[1]=C_i_block_ref(t2,C_fix(2));
((C_proc)(void*)(*((C_word*)t4+1)))(2,av2);}}

/* crypto-ffi#share-x in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1981(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2=av[2];
C_word t3;
C_word t4;
C_word *a;
if(c!=3) C_bad_argc_2(c,3,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,1)))){
C_save_and_reclaim((void *)f_1981,c,av);}
t3=C_i_check_structure_2(t2,lf[65],lf[71]);
t4=t1;{
C_word *av2=av;
av2[0]=t4;
av2[1]=C_i_block_ref(t2,C_fix(3));
((C_proc)(void*)(*((C_word*)t4+1)))(2,av2);}}

/* crypto-ffi#share-y in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1990(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2=av[2];
C_word t3;
C_word t4;
C_word *a;
if(c!=3) C_bad_argc_2(c,3,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,1)))){
C_save_and_reclaim((void *)f_1990,c,av);}
t3=C_i_check_structure_2(t2,lf[65],lf[73]);
t4=t1;{
C_word *av2=av;
av2[0]=t4;
av2[1]=C_i_block_ref(t2,C_fix(4));
((C_proc)(void*)(*((C_word*)t4+1)))(2,av2);}}

/* crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_1999(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2=av[2];
C_word t3;
C_word *a;
if(c<3) C_bad_min_argc_2(c,3,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand((c-3)*C_SIZEOF_PAIR +8,c,4)))){
C_save_and_reclaim((void*)f_1999,c,av);}
a=C_alloc((c-3)*C_SIZEOF_PAIR+8);
t3=C_build_rest(&a,c,3,av);
C_word t4;
C_word t5;
C_word t6;
t4=(*a=C_CLOSURE_TYPE|4,a[1]=(C_word)f_2003,a[2]=t1,a[3]=t2,a[4]=t3,tmp=(C_word)a,a+=5,tmp);
t5=(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_2214,a[2]=((C_word)li36),tmp=(C_word)a,a+=3,tmp);
C_trace(C_text("crypto-ffi.scm:533: ##sys#get-keyword"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[86]+1));
C_word *av2;
if(c >= 5) {
  av2=av;
} else {
  av2=C_alloc(5);
}
av2[0]=*((C_word*)lf[86]+1);
av2[1]=t4;
av2[2]=lf[88];
av2[3]=t3;
av2[4]=t5;
tp(5,av2);}}

/* k2001 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2003(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(8,c,4)))){
C_save_and_reclaim((void *)f_2003,c,av);}
a=C_alloc(8);
t2=(*a=C_CLOSURE_TYPE|4,a[1]=(C_word)f_2006,a[2]=((C_word*)t0)[2],a[3]=t1,a[4]=((C_word*)t0)[3],tmp=(C_word)a,a+=5,tmp);
t3=(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_2211,a[2]=((C_word)li35),tmp=(C_word)a,a+=3,tmp);
C_trace(C_text("crypto-ffi.scm:533: ##sys#get-keyword"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[86]+1));
C_word *av2;
if(c >= 5) {
  av2=av;
} else {
  av2=C_alloc(5);
}
av2[0]=*((C_word*)lf[86]+1);
av2[1]=t2;
av2[2]=lf[87];
av2[3]=((C_word*)t0)[4];
av2[4]=t3;
tp(5,av2);}}

/* k2004 in k2001 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2006(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(6,c,2)))){
C_save_and_reclaim((void *)f_2006,c,av);}
a=C_alloc(6);
t2=(*a=C_CLOSURE_TYPE|5,a[1]=(C_word)f_2009,a[2]=((C_word*)t0)[2],a[3]=t1,a[4]=((C_word*)t0)[3],a[5]=((C_word*)t0)[4],tmp=(C_word)a,a+=6,tmp);
if(C_truep(C_i_less_or_equalp(((C_word*)t0)[3],t1))){
t3=t2;{
C_word *av2=av;
av2[0]=t3;
av2[1]=C_SCHEME_UNDEFINED;
f_2009(2,av2);}}
else{
C_trace(C_text("crypto-ffi.scm:543: chicken.base#error"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[39]+1));
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[39]+1);
av2[1]=t2;
av2[2]=lf[85];
tp(3,av2);}}}

/* k2007 in k2004 in k2001 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2009(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(6,c,2)))){
C_save_and_reclaim((void *)f_2009,c,av);}
a=C_alloc(6);
t2=(*a=C_CLOSURE_TYPE|5,a[1]=(C_word)f_2012,a[2]=((C_word*)t0)[2],a[3]=((C_word*)t0)[3],a[4]=((C_word*)t0)[4],a[5]=((C_word*)t0)[5],tmp=(C_word)a,a+=6,tmp);
if(C_truep(C_i_greaterp(((C_word*)t0)[4],C_fix(1)))){
t3=t2;{
C_word *av2=av;
av2[0]=t3;
av2[1]=C_SCHEME_UNDEFINED;
f_2012(2,av2);}}
else{
C_trace(C_text("crypto-ffi.scm:546: chicken.base#error"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[39]+1));
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[39]+1);
av2[1]=t2;
av2[2]=lf[84];
tp(3,av2);}}}

/* k2010 in k2007 in k2004 in k2001 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2012(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(5,c,2)))){
C_save_and_reclaim((void *)f_2012,c,av);}
a=C_alloc(5);
t2=(*a=C_CLOSURE_TYPE|4,a[1]=(C_word)f_2015,a[2]=((C_word*)t0)[2],a[3]=((C_word*)t0)[3],a[4]=((C_word*)t0)[4],tmp=(C_word)a,a+=5,tmp);
C_trace(C_text("crypto-ffi.scm:548: srfi-4#blob->u8vector"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[83]);
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[83]+1);
av2[1]=t2;
av2[2]=((C_word*)t0)[5];
tp(3,av2);}}

/* k2013 in k2010 in k2007 in k2004 in k2001 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2015(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(7,c,2)))){
C_save_and_reclaim((void *)f_2015,c,av);}
a=C_alloc(7);
t2=C_i_u8vector_length(t1);
t3=(*a=C_CLOSURE_TYPE|6,a[1]=(C_word)f_2021,a[2]=((C_word*)t0)[2],a[3]=((C_word*)t0)[3],a[4]=((C_word*)t0)[4],a[5]=t2,a[6]=t1,tmp=(C_word)a,a+=7,tmp);
C_trace(C_text("crypto-ffi.scm:550: scheme#make-vector"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[81]+1));
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[81]+1);
av2[1]=t3;
av2[2]=((C_word*)t0)[3];
tp(3,av2);}}

/* k2019 in k2013 in k2010 in k2007 in k2004 in k2001 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2021(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word t5;
C_word t6;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(17,c,3)))){
C_save_and_reclaim((void *)f_2021,c,av);}
a=C_alloc(17);
t2=(*a=C_CLOSURE_TYPE|7,a[1]=(C_word)f_2024,a[2]=((C_word*)t0)[2],a[3]=t1,a[4]=((C_word*)t0)[3],a[5]=((C_word*)t0)[4],a[6]=((C_word*)t0)[5],a[7]=((C_word*)t0)[6],tmp=(C_word)a,a+=8,tmp);
t3=C_SCHEME_UNDEFINED;
t4=(*a=C_VECTOR_TYPE|1,a[1]=t3,tmp=(C_word)a,a+=2,tmp);
t5=C_set_block_item(t4,0,(*a=C_CLOSURE_TYPE|6,a[1]=(C_word)f_2176,a[2]=((C_word*)t0)[3],a[3]=t1,a[4]=t4,a[5]=((C_word*)t0)[5],a[6]=((C_word)li34),tmp=(C_word)a,a+=7,tmp));
t6=((C_word*)t4)[1];
f_2176(t6,t2,C_fix(0));}

/* k2022 in k2019 in k2013 in k2010 in k2007 in k2004 in k2001 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2024(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word t5;
C_word t6;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(17,c,3)))){
C_save_and_reclaim((void *)f_2024,c,av);}
a=C_alloc(17);
t2=(*a=C_CLOSURE_TYPE|5,a[1]=(C_word)f_2027,a[2]=((C_word*)t0)[2],a[3]=((C_word*)t0)[3],a[4]=((C_word*)t0)[4],a[5]=((C_word*)t0)[5],tmp=(C_word)a,a+=6,tmp);
t3=C_SCHEME_UNDEFINED;
t4=(*a=C_VECTOR_TYPE|1,a[1]=t3,tmp=(C_word)a,a+=2,tmp);
t5=C_set_block_item(t4,0,(*a=C_CLOSURE_TYPE|8,a[1]=(C_word)f_2086,a[2]=((C_word*)t0)[6],a[3]=((C_word*)t0)[7],a[4]=t4,a[5]=((C_word*)t0)[4],a[6]=((C_word*)t0)[3],a[7]=((C_word*)t0)[5],a[8]=((C_word)li33),tmp=(C_word)a,a+=9,tmp));
t6=((C_word*)t4)[1];
f_2086(t6,t2,C_fix(0));}

/* k2025 in k2022 in k2019 in k2013 in k2010 in k2007 in k2004 in k2001 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2027(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word t5;
C_word t6;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(13,c,3)))){
C_save_and_reclaim((void *)f_2027,c,av);}
a=C_alloc(13);
t2=(*a=C_CLOSURE_TYPE|3,a[1]=(C_word)f_2030,a[2]=((C_word*)t0)[2],a[3]=((C_word*)t0)[3],tmp=(C_word)a,a+=4,tmp);
t3=C_SCHEME_UNDEFINED;
t4=(*a=C_VECTOR_TYPE|1,a[1]=t3,tmp=(C_word)a,a+=2,tmp);
t5=C_set_block_item(t4,0,(*a=C_CLOSURE_TYPE|6,a[1]=(C_word)f_2035,a[2]=((C_word*)t0)[4],a[3]=((C_word*)t0)[5],a[4]=((C_word*)t0)[3],a[5]=t4,a[6]=((C_word)li29),tmp=(C_word)a,a+=7,tmp));
t6=((C_word*)t4)[1];
f_2035(t6,t2,C_fix(0));}

/* k2028 in k2025 in k2022 in k2019 in k2013 in k2010 in k2007 in k2004 in k2001 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2030(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,2)))){
C_save_and_reclaim((void *)f_2030,c,av);}
C_trace(C_text("crypto-ffi.scm:589: scheme#vector->list"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[75]+1));
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[75]+1);
av2[1]=((C_word*)t0)[2];
av2[2]=((C_word*)t0)[3];
tp(3,av2);}}

/* doloop508 in k2025 in k2022 in k2019 in k2013 in k2010 in k2007 in k2004 in k2001 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_fcall f_2035(C_word t0,C_word t1,C_word t2){
C_word tmp;
C_word t3;
C_word t4;
C_word t5;
C_word t6;
C_word t7;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(42,0,2)))){
C_save_and_reclaim_args((void *)trf_2035,3,t0,t1,t2);}
a=C_alloc(42);
if(C_truep(C_i_nequalp(t2,((C_word*)t0)[2]))){
t3=C_SCHEME_UNDEFINED;
t4=t1;{
C_word av2[2];
av2[0]=t4;
av2[1]=t3;
((C_proc)(void*)(*((C_word*)t4+1)))(2,av2);}}
else{
t3=(*a=C_CLOSURE_TYPE|6,a[1]=(C_word)f_2060,a[2]=t2,a[3]=((C_word*)t0)[3],a[4]=((C_word*)t0)[4],a[5]=((C_word*)t0)[5],a[6]=t1,tmp=(C_word)a,a+=7,tmp);
t4=(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_2076,a[2]=t3,tmp=(C_word)a,a+=3,tmp);
t5=(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_2080,a[2]=t4,tmp=(C_word)a,a+=3,tmp);
t6=C_s_a_i_plus(&a,2,t2,C_fix(1));
C_trace(C_text("crypto-ffi.scm:584: scheme#number->string"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[80]+1));
C_word av2[3];
av2[0]=*((C_word*)lf[80]+1);
av2[1]=t5;
av2[2]=t6;
tp(3,av2);}}}

/* k2058 in doloop508 in k2025 in k2022 in k2019 in k2013 in k2010 in k2007 in k2004 in k2001 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2060(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(38,c,2)))){
C_save_and_reclaim((void *)f_2060,c,av);}
a=C_alloc(38);
t2=C_s_a_i_plus(&a,2,((C_word*)t0)[2],C_fix(1));
t3=(*a=C_CLOSURE_TYPE|8,a[1]=(C_word)f_2068,a[2]=t1,a[3]=((C_word*)t0)[3],a[4]=t2,a[5]=((C_word*)t0)[4],a[6]=((C_word*)t0)[2],a[7]=((C_word*)t0)[5],a[8]=((C_word*)t0)[6],tmp=(C_word)a,a+=9,tmp);
C_trace(C_text("crypto-ffi.scm:587: srfi-4#u8vector->blob"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[76]);
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[76]+1);
av2[1]=t3;
av2[2]=C_i_vector_ref(((C_word*)t0)[4],((C_word*)t0)[2]);
tp(3,av2);}}

/* k2066 in k2058 in doloop508 in k2025 in k2022 in k2019 in k2013 in k2010 in k2007 in k2004 in k2001 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2068(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word t5;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(35,c,2)))){
C_save_and_reclaim((void *)f_2068,c,av);}
a=C_alloc(35);
t2=C_a_i_record5(&a,5,lf[65],((C_word*)t0)[2],((C_word*)t0)[3],((C_word*)t0)[4],t1);
t3=C_i_vector_set(((C_word*)t0)[5],((C_word*)t0)[6],t2);
t4=C_s_a_i_plus(&a,2,((C_word*)t0)[6],C_fix(1));
t5=((C_word*)((C_word*)t0)[7])[1];
f_2035(t5,((C_word*)t0)[8],t4);}

/* k2074 in doloop508 in k2025 in k2022 in k2019 in k2013 in k2010 in k2007 in k2004 in k2001 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2076(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,2)))){
C_save_and_reclaim((void *)f_2076,c,av);}
C_trace(C_text("crypto-ffi.scm:584: scheme#string->symbol"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[77]+1));
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[77]+1);
av2[1]=((C_word*)t0)[2];
av2[2]=t1;
tp(3,av2);}}

/* k2078 in doloop508 in k2025 in k2022 in k2019 in k2013 in k2010 in k2007 in k2004 in k2001 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2080(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,3)))){
C_save_and_reclaim((void *)f_2080,c,av);}
C_trace(C_text("crypto-ffi.scm:584: scheme#string-append"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[78]+1));
C_word *av2;
if(c >= 4) {
  av2=av;
} else {
  av2=C_alloc(4);
}
av2[0]=*((C_word*)lf[78]+1);
av2[1]=((C_word*)t0)[2];
av2[2]=lf[79];
av2[3]=t1;
tp(4,av2);}}

/* doloop507 in k2022 in k2019 in k2013 in k2010 in k2007 in k2004 in k2001 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_fcall f_2086(C_word t0,C_word t1,C_word t2){
C_word tmp;
C_word t3;
C_word t4;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(9,0,2)))){
C_save_and_reclaim_args((void *)trf_2086,3,t0,t1,t2);}
a=C_alloc(9);
if(C_truep(C_i_nequalp(t2,((C_word*)t0)[2]))){
t3=C_SCHEME_UNDEFINED;
t4=t1;{
C_word av2[2];
av2[0]=t4;
av2[1]=t3;
((C_proc)(void*)(*((C_word*)t4+1)))(2,av2);}}
else{
t3=(*a=C_CLOSURE_TYPE|8,a[1]=(C_word)f_2096,a[2]=((C_word*)t0)[3],a[3]=t2,a[4]=((C_word*)t0)[4],a[5]=t1,a[6]=((C_word*)t0)[5],a[7]=((C_word*)t0)[6],a[8]=((C_word*)t0)[7],tmp=(C_word)a,a+=9,tmp);
C_trace(C_text("crypto-ffi.scm:563: scheme#make-vector"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[81]+1));
C_word av2[3];
av2[0]=*((C_word*)lf[81]+1);
av2[1]=t3;
av2[2]=((C_word*)t0)[7];
tp(3,av2);}}}

/* k2094 in doloop507 in k2022 in k2019 in k2013 in k2010 in k2007 in k2004 in k2001 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2096(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word t5;
C_word t6;
C_word t7;
C_word t8;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(16,c,3)))){
C_save_and_reclaim((void *)f_2096,c,av);}
a=C_alloc(16);
t2=C_i_u8vector_ref(((C_word*)t0)[2],((C_word*)t0)[3]);
t3=C_i_vector_set(t1,C_fix(0),t2);
t4=(*a=C_CLOSURE_TYPE|7,a[1]=(C_word)f_2102,a[2]=((C_word*)t0)[3],a[3]=((C_word*)t0)[4],a[4]=((C_word*)t0)[5],a[5]=((C_word*)t0)[6],a[6]=((C_word*)t0)[7],a[7]=t1,tmp=(C_word)a,a+=8,tmp);
t5=C_SCHEME_UNDEFINED;
t6=(*a=C_VECTOR_TYPE|1,a[1]=t5,tmp=(C_word)a,a+=2,tmp);
t7=C_set_block_item(t6,0,(*a=C_CLOSURE_TYPE|5,a[1]=(C_word)f_2149,a[2]=((C_word*)t0)[8],a[3]=t1,a[4]=t6,a[5]=((C_word)li32),tmp=(C_word)a,a+=6,tmp));
t8=((C_word*)t6)[1];
f_2149(t8,t4,C_fix(1));}

/* k2100 in k2094 in doloop507 in k2022 in k2019 in k2013 in k2010 in k2007 in k2004 in k2001 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2102(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word t5;
C_word t6;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(15,c,3)))){
C_save_and_reclaim((void *)f_2102,c,av);}
a=C_alloc(15);
t2=(*a=C_CLOSURE_TYPE|4,a[1]=(C_word)f_2105,a[2]=((C_word*)t0)[2],a[3]=((C_word*)t0)[3],a[4]=((C_word*)t0)[4],tmp=(C_word)a,a+=5,tmp);
t3=C_SCHEME_UNDEFINED;
t4=(*a=C_VECTOR_TYPE|1,a[1]=t3,tmp=(C_word)a,a+=2,tmp);
t5=C_set_block_item(t4,0,(*a=C_CLOSURE_TYPE|7,a[1]=(C_word)f_2114,a[2]=((C_word*)t0)[5],a[3]=((C_word*)t0)[6],a[4]=((C_word*)t0)[2],a[5]=t4,a[6]=((C_word*)t0)[7],a[7]=((C_word)li31),tmp=(C_word)a,a+=8,tmp));
t6=((C_word*)t4)[1];
f_2114(t6,t2,C_fix(1));}

/* k2103 in k2100 in k2094 in doloop507 in k2022 in k2019 in k2013 in k2010 in k2007 in k2004 in k2001 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2105(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(29,c,2)))){
C_save_and_reclaim((void *)f_2105,c,av);}
a=C_alloc(29);
t2=C_s_a_i_plus(&a,2,((C_word*)t0)[2],C_fix(1));
t3=((C_word*)((C_word*)t0)[3])[1];
f_2086(t3,((C_word*)t0)[4],t2);}

/* doloop517 in k2100 in k2094 in doloop507 in k2022 in k2019 in k2013 in k2010 in k2007 in k2004 in k2001 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_fcall f_2114(C_word t0,C_word t1,C_word t2){
C_word tmp;
C_word t3;
C_word t4;
C_word t5;
C_word t6;
C_word t7;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(40,0,2)))){
C_save_and_reclaim_args((void *)trf_2114,3,t0,t1,t2);}
a=C_alloc(40);
if(C_truep(C_i_greaterp(t2,((C_word*)t0)[2]))){
t3=C_SCHEME_UNDEFINED;
t4=t1;{
C_word av2[2];
av2[0]=t4;
av2[1]=t3;
((C_proc)(void*)(*((C_word*)t4+1)))(2,av2);}}
else{
t3=C_s_a_i_minus(&a,2,t2,C_fix(1));
t4=C_i_vector_ref(((C_word*)t0)[3],t3);
t5=(*a=C_CLOSURE_TYPE|6,a[1]=(C_word)f_2139,a[2]=t4,a[3]=((C_word*)t0)[4],a[4]=t2,a[5]=((C_word*)t0)[5],a[6]=t1,tmp=(C_word)a,a+=7,tmp);
t6=(*a=C_CLOSURE_TYPE|3,a[1]=(C_word)f_2143,a[2]=t2,a[3]=t5,tmp=(C_word)a,a+=4,tmp);
C_trace(C_text("crypto-ffi.scm:577: scheme#vector->list"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[75]+1));
C_word av2[3];
av2[0]=*((C_word*)lf[75]+1);
av2[1]=t6;
av2[2]=((C_word*)t0)[6];
tp(3,av2);}}}

/* k2137 in doloop517 in k2100 in k2094 in doloop507 in k2022 in k2019 in k2013 in k2010 in k2007 in k2004 in k2001 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 in ... */
static void C_ccall f_2139(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(29,c,2)))){
C_save_and_reclaim((void *)f_2139,c,av);}
a=C_alloc(29);
t2=C_i_u8vector_set(((C_word*)t0)[2],((C_word*)t0)[3],t1);
t3=C_s_a_i_plus(&a,2,((C_word*)t0)[4],C_fix(1));
t4=((C_word*)((C_word*)t0)[5])[1];
f_2114(t4,((C_word*)t0)[6],t3);}

/* k2141 in doloop517 in k2100 in k2094 in doloop507 in k2022 in k2019 in k2013 in k2010 in k2007 in k2004 in k2001 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 in ... */
static void C_ccall f_2143(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word t5;
C_word t6;
C_word t7;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(37,c,4)))){
C_save_and_reclaim((void *)f_2143,c,av);}
a=C_alloc(37);
t2=C_i_length(t1);
t3=C_s_a_i_minus(&a,2,t2,C_fix(1));
t4=C_SCHEME_UNDEFINED;
t5=(*a=C_VECTOR_TYPE|1,a[1]=t4,tmp=(C_word)a,a+=2,tmp);
t6=C_set_block_item(t5,0,(*a=C_CLOSURE_TYPE|5,a[1]=(C_word)f_1918,a[2]=t5,a[3]=t1,a[4]=((C_word*)t0)[2],a[5]=((C_word)li30),tmp=(C_word)a,a+=6,tmp));
t7=((C_word*)t5)[1];
f_1918(t7,((C_word*)t0)[3],t3,C_fix(0));}

/* doloop516 in k2094 in doloop507 in k2022 in k2019 in k2013 in k2010 in k2007 in k2004 in k2001 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_fcall f_2149(C_word t0,C_word t1,C_word t2){
C_word tmp;
C_word t3;
C_word t4;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(6,0,2)))){
C_save_and_reclaim_args((void *)trf_2149,3,t0,t1,t2);}
a=C_alloc(6);
if(C_truep(C_i_nequalp(t2,((C_word*)t0)[2]))){
t3=C_SCHEME_UNDEFINED;
t4=t1;{
C_word av2[2];
av2[0]=t4;
av2[1]=t3;
((C_proc)(void*)(*((C_word*)t4+1)))(2,av2);}}
else{
t3=(*a=C_CLOSURE_TYPE|5,a[1]=(C_word)f_2170,a[2]=((C_word*)t0)[3],a[3]=t2,a[4]=((C_word*)t0)[4],a[5]=t1,tmp=(C_word)a,a+=6,tmp);
C_trace(C_text("crypto-ffi.scm:570: random-u8"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[23]);
C_word av2[2];
av2[0]=*((C_word*)lf[23]+1);
av2[1]=t3;
tp(2,av2);}}}

/* k2168 in doloop516 in k2094 in doloop507 in k2022 in k2019 in k2013 in k2010 in k2007 in k2004 in k2001 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2170(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(29,c,2)))){
C_save_and_reclaim((void *)f_2170,c,av);}
a=C_alloc(29);
t2=C_i_vector_set(((C_word*)t0)[2],((C_word*)t0)[3],t1);
t3=C_s_a_i_plus(&a,2,((C_word*)t0)[3],C_fix(1));
t4=((C_word*)((C_word*)t0)[4])[1];
f_2149(t4,((C_word*)t0)[5],t3);}

/* doloop506 in k2019 in k2013 in k2010 in k2007 in k2004 in k2001 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_fcall f_2176(C_word t0,C_word t1,C_word t2){
C_word tmp;
C_word t3;
C_word t4;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(6,0,2)))){
C_save_and_reclaim_args((void *)trf_2176,3,t0,t1,t2);}
a=C_alloc(6);
if(C_truep(C_i_nequalp(t2,((C_word*)t0)[2]))){
t3=C_SCHEME_UNDEFINED;
t4=t1;{
C_word av2[2];
av2[0]=t4;
av2[1]=t3;
((C_proc)(void*)(*((C_word*)t4+1)))(2,av2);}}
else{
t3=(*a=C_CLOSURE_TYPE|5,a[1]=(C_word)f_2197,a[2]=((C_word*)t0)[3],a[3]=t2,a[4]=((C_word*)t0)[4],a[5]=t1,tmp=(C_word)a,a+=6,tmp);
C_trace(C_text("crypto-ffi.scm:555: srfi-4#make-u8vector"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[82]);
C_word av2[3];
av2[0]=*((C_word*)lf[82]+1);
av2[1]=t3;
av2[2]=((C_word*)t0)[5];
tp(3,av2);}}}

/* k2195 in doloop506 in k2019 in k2013 in k2010 in k2007 in k2004 in k2001 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2197(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(29,c,2)))){
C_save_and_reclaim((void *)f_2197,c,av);}
a=C_alloc(29);
t2=C_i_vector_set(((C_word*)t0)[2],((C_word*)t0)[3],t1);
t3=C_s_a_i_plus(&a,2,((C_word*)t0)[3],C_fix(1));
t4=((C_word*)((C_word*)t0)[4])[1];
f_2176(t4,((C_word*)t0)[5],t3);}

/* a2210 in k2001 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2211(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word *a;
if(c!=2) C_bad_argc_2(c,2,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,1)))){
C_save_and_reclaim((void *)f_2211,c,av);}
t2=t1;{
C_word *av2=av;
av2[0]=t2;
av2[1]=C_fix(5);
((C_proc)(void*)(*((C_word*)t2+1)))(2,av2);}}

/* a2213 in crypto-ffi#shamir-split in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2214(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word *a;
if(c!=2) C_bad_argc_2(c,2,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,1)))){
C_save_and_reclaim((void *)f_2214,c,av);}
t2=t1;{
C_word *av2=av;
av2[0]=t2;
av2[1]=C_fix(3);
((C_proc)(void*)(*((C_word*)t2+1)))(2,av2);}}

/* crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2217(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2=av[2];
C_word t3;
C_word t4;
C_word *a;
if(c!=3) C_bad_argc_2(c,3,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(4,c,2)))){
C_save_and_reclaim((void *)f_2217,c,av);}
a=C_alloc(4);
t3=(*a=C_CLOSURE_TYPE|3,a[1]=(C_word)f_2221,a[2]=t2,a[3]=t1,tmp=(C_word)a,a+=4,tmp);
if(C_truep(C_i_nullp(t2))){
C_trace(C_text("crypto-ffi.scm:599: chicken.base#error"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[39]+1));
C_word *av2=av;
av2[0]=*((C_word*)lf[39]+1);
av2[1]=t3;
av2[2]=lf[98];
tp(3,av2);}}
else{
t4=t3;{
C_word *av2=av;
av2[0]=t4;
av2[1]=C_SCHEME_UNDEFINED;
f_2221(2,av2);}}}

/* k2219 in crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2221(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(4,c,2)))){
C_save_and_reclaim((void *)f_2221,c,av);}
a=C_alloc(4);
t2=(*a=C_CLOSURE_TYPE|3,a[1]=(C_word)f_2224,a[2]=((C_word*)t0)[2],a[3]=((C_word*)t0)[3],tmp=(C_word)a,a+=4,tmp);
C_trace(C_text("crypto-ffi.scm:601: share-threshold"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[68]);
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[68]+1);
av2[1]=t2;
av2[2]=C_i_car(((C_word*)t0)[2]);
tp(3,av2);}}

/* k2222 in k2219 in crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2224(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word t5;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(10,c,2)))){
C_save_and_reclaim((void *)f_2224,c,av);}
a=C_alloc(10);
t2=C_i_length(((C_word*)t0)[2]);
t3=(*a=C_CLOSURE_TYPE|4,a[1]=(C_word)f_2230,a[2]=((C_word*)t0)[3],a[3]=t1,a[4]=((C_word*)t0)[2],tmp=(C_word)a,a+=5,tmp);
if(C_truep(C_i_greater_or_equalp(t2,t1))){
t4=t3;{
C_word *av2=av;
av2[0]=t4;
av2[1]=C_SCHEME_UNDEFINED;
f_2230(2,av2);}}
else{
t4=(*a=C_CLOSURE_TYPE|4,a[1]=(C_word)f_2379,a[2]=t3,a[3]=t2,a[4]=t1,tmp=(C_word)a,a+=5,tmp);
C_trace(C_text("crypto-ffi.scm:605: chicken.base#open-output-string"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[97]);
C_word *av2=av;
av2[0]=*((C_word*)lf[97]+1);
av2[1]=t4;
tp(2,av2);}}}

/* k2228 in k2222 in k2219 in crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2230(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(4,c,3)))){
C_save_and_reclaim((void *)f_2230,c,av);}
a=C_alloc(4);
t2=(*a=C_CLOSURE_TYPE|3,a[1]=(C_word)f_2233,a[2]=((C_word*)t0)[2],a[3]=((C_word*)t0)[3],tmp=(C_word)a,a+=4,tmp);
C_trace(C_text("crypto-ffi.scm:608: srfi-1#take"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[90]);
C_word *av2;
if(c >= 4) {
  av2=av;
} else {
  av2=C_alloc(4);
}
av2[0]=*((C_word*)lf[90]+1);
av2[1]=t2;
av2[2]=((C_word*)t0)[4];
av2[3]=((C_word*)t0)[3];
tp(4,av2);}}

/* k2231 in k2228 in k2222 in k2219 in crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2233(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(8,c,2)))){
C_save_and_reclaim((void *)f_2233,c,av);}
a=C_alloc(8);
t2=(*a=C_CLOSURE_TYPE|4,a[1]=(C_word)f_2236,a[2]=((C_word*)t0)[2],a[3]=((C_word*)t0)[3],a[4]=t1,tmp=(C_word)a,a+=5,tmp);
t3=(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_2365,a[2]=t2,tmp=(C_word)a,a+=3,tmp);
C_trace(C_text("crypto-ffi.scm:609: share-y"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[72]);
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[72]+1);
av2[1]=t3;
av2[2]=C_i_car(t1);
tp(3,av2);}}

/* k2234 in k2231 in k2228 in k2222 in k2219 in crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2236(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(6,c,2)))){
C_save_and_reclaim((void *)f_2236,c,av);}
a=C_alloc(6);
t2=(*a=C_CLOSURE_TYPE|5,a[1]=(C_word)f_2239,a[2]=((C_word*)t0)[2],a[3]=t1,a[4]=((C_word*)t0)[3],a[5]=((C_word*)t0)[4],tmp=(C_word)a,a+=6,tmp);
C_trace(C_text("crypto-ffi.scm:610: srfi-4#make-u8vector"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[82]);
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[82]+1);
av2[1]=t2;
av2[2]=t1;
tp(3,av2);}}

/* k2237 in k2234 in k2231 in k2228 in k2222 in k2219 in crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2239(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word t5;
C_word t6;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(14,c,3)))){
C_save_and_reclaim((void *)f_2239,c,av);}
a=C_alloc(14);
t2=(*a=C_CLOSURE_TYPE|3,a[1]=(C_word)f_2242,a[2]=((C_word*)t0)[2],a[3]=t1,tmp=(C_word)a,a+=4,tmp);
t3=C_SCHEME_UNDEFINED;
t4=(*a=C_VECTOR_TYPE|1,a[1]=t3,tmp=(C_word)a,a+=2,tmp);
t5=C_set_block_item(t4,0,(*a=C_CLOSURE_TYPE|7,a[1]=(C_word)f_2247,a[2]=((C_word*)t0)[3],a[3]=t1,a[4]=t4,a[5]=((C_word*)t0)[4],a[6]=((C_word*)t0)[5],a[7]=((C_word)li40),tmp=(C_word)a,a+=8,tmp));
t6=((C_word*)t4)[1];
f_2247(t6,t2,C_fix(0));}

/* k2240 in k2237 in k2234 in k2231 in k2228 in k2222 in k2219 in crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2242(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,2)))){
C_save_and_reclaim((void *)f_2242,c,av);}
C_trace(C_text("crypto-ffi.scm:642: srfi-4#u8vector->blob"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[76]);
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[76]+1);
av2[1]=((C_word*)t0)[2];
av2[2]=((C_word*)t0)[3];
tp(3,av2);}}

/* doloop559 in k2237 in k2234 in k2231 in k2228 in k2222 in k2219 in crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_fcall f_2247(C_word t0,C_word t1,C_word t2){
C_word tmp;
C_word t3;
C_word t4;
C_word t5;
C_word t6;
C_word t7;
C_word t8;
C_word t9;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(19,0,3)))){
C_save_and_reclaim_args((void *)trf_2247,3,t0,t1,t2);}
a=C_alloc(19);
if(C_truep(C_i_nequalp(t2,((C_word*)t0)[2]))){
t3=C_SCHEME_UNDEFINED;
t4=t1;{
C_word av2[2];
av2[0]=t4;
av2[1]=t3;
((C_proc)(void*)(*((C_word*)t4+1)))(2,av2);}}
else{
t3=C_fix(0);
t4=(*a=C_VECTOR_TYPE|1,a[1]=t3,tmp=(C_word)a,a+=2,tmp);
t5=(*a=C_CLOSURE_TYPE|6,a[1]=(C_word)f_2257,a[2]=((C_word*)t0)[3],a[3]=t2,a[4]=t4,a[5]=((C_word*)t0)[4],a[6]=t1,tmp=(C_word)a,a+=7,tmp);
t6=C_SCHEME_UNDEFINED;
t7=(*a=C_VECTOR_TYPE|1,a[1]=t6,tmp=(C_word)a,a+=2,tmp);
t8=C_set_block_item(t7,0,(*a=C_CLOSURE_TYPE|7,a[1]=(C_word)f_2269,a[2]=((C_word*)t0)[5],a[3]=t2,a[4]=t4,a[5]=t7,a[6]=((C_word*)t0)[6],a[7]=((C_word)li39),tmp=(C_word)a,a+=8,tmp));
t9=((C_word*)t7)[1];
f_2269(t9,t5,C_fix(0));}}

/* k2255 in doloop559 in k2237 in k2234 in k2231 in k2228 in k2222 in k2219 in crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2257(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(29,c,2)))){
C_save_and_reclaim((void *)f_2257,c,av);}
a=C_alloc(29);
t2=C_i_u8vector_set(((C_word*)t0)[2],((C_word*)t0)[3],((C_word*)((C_word*)t0)[4])[1]);
t3=C_s_a_i_plus(&a,2,((C_word*)t0)[3],C_fix(1));
t4=((C_word*)((C_word*)t0)[5])[1];
f_2247(t4,((C_word*)t0)[6],t3);}

/* doloop563 in doloop559 in k2237 in k2234 in k2231 in k2228 in k2222 in k2219 in crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_fcall f_2269(C_word t0,C_word t1,C_word t2){
C_word tmp;
C_word t3;
C_word t4;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(9,0,2)))){
C_save_and_reclaim_args((void *)trf_2269,3,t0,t1,t2);}
a=C_alloc(9);
if(C_truep(C_i_nequalp(t2,((C_word*)t0)[2]))){
t3=C_SCHEME_UNDEFINED;
t4=t1;{
C_word av2[2];
av2[0]=t4;
av2[1]=t3;
((C_proc)(void*)(*((C_word*)t4+1)))(2,av2);}}
else{
t3=(*a=C_CLOSURE_TYPE|8,a[1]=(C_word)f_2279,a[2]=((C_word*)t0)[3],a[3]=((C_word*)t0)[4],a[4]=t2,a[5]=((C_word*)t0)[5],a[6]=t1,a[7]=((C_word*)t0)[2],a[8]=((C_word*)t0)[6],tmp=(C_word)a,a+=9,tmp);
C_trace(C_text("crypto-ffi.scm:621: share-x"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[70]);
C_word av2[3];
av2[0]=*((C_word*)lf[70]+1);
av2[1]=t3;
av2[2]=C_i_list_ref(((C_word*)t0)[6],t2);
tp(3,av2);}}}

/* k2277 in doloop563 in doloop559 in k2237 in k2234 in k2231 in k2228 in k2222 in k2219 in crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2279(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(13,c,2)))){
C_save_and_reclaim((void *)f_2279,c,av);}
a=C_alloc(13);
t2=(*a=C_CLOSURE_TYPE|9,a[1]=(C_word)f_2349,a[2]=((C_word*)t0)[2],a[3]=((C_word*)t0)[3],a[4]=((C_word*)t0)[4],a[5]=((C_word*)t0)[5],a[6]=((C_word*)t0)[6],a[7]=((C_word*)t0)[7],a[8]=t1,a[9]=((C_word*)t0)[8],tmp=(C_word)a,a+=10,tmp);
t3=(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_2353,a[2]=t2,tmp=(C_word)a,a+=3,tmp);
C_trace(C_text("crypto-ffi.scm:622: share-y"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[72]);
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[72]+1);
av2[1]=t3;
av2[2]=C_i_list_ref(((C_word*)t0)[8],((C_word*)t0)[4]);
tp(3,av2);}}

/* k2283 in k2347 in k2277 in doloop563 in doloop559 in k2237 in k2234 in k2231 in k2228 in k2222 in k2219 in crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2285(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(10,c,3)))){
C_save_and_reclaim((void *)f_2285,c,av);}
a=C_alloc(10);
t2=(*a=C_CLOSURE_TYPE|5,a[1]=(C_word)f_2289,a[2]=((C_word*)t0)[2],a[3]=((C_word*)t0)[3],a[4]=((C_word*)t0)[4],a[5]=((C_word*)t0)[5],tmp=(C_word)a,a+=6,tmp);
t3=(*a=C_CLOSURE_TYPE|3,a[1]=(C_word)f_2300,a[2]=t2,a[3]=((C_word*)t0)[2],tmp=(C_word)a,a+=4,tmp);
C_trace(C_text("crypto-ffi.scm:638: gf256-mul"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[62]);
C_word *av2;
if(c >= 4) {
  av2=av;
} else {
  av2=C_alloc(4);
}
av2[0]=*((C_word*)lf[62]+1);
av2[1]=t3;
av2[2]=((C_word*)t0)[6];
av2[3]=((C_word*)((C_word*)t0)[7])[1];
tp(4,av2);}}

/* k2287 in k2283 in k2347 in k2277 in doloop563 in doloop559 in k2237 in k2234 in k2231 in k2228 in k2222 in k2219 in crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 in ... */
static void C_ccall f_2289(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(29,c,2)))){
C_save_and_reclaim((void *)f_2289,c,av);}
a=C_alloc(29);
t2=C_mutate(((C_word *)((C_word*)t0)[2])+1,t1);
t3=C_s_a_i_plus(&a,2,((C_word*)t0)[3],C_fix(1));
t4=((C_word*)((C_word*)t0)[4])[1];
f_2269(t4,((C_word*)t0)[5],t3);}

/* k2298 in k2283 in k2347 in k2277 in doloop563 in doloop559 in k2237 in k2234 in k2231 in k2228 in k2222 in k2219 in crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 in ... */
static void C_ccall f_2300(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,3)))){
C_save_and_reclaim((void *)f_2300,c,av);}
C_trace(C_text("crypto-ffi.scm:638: gf256-add"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[61]);
C_word *av2;
if(c >= 4) {
  av2=av;
} else {
  av2=C_alloc(4);
}
av2[0]=*((C_word*)lf[61]+1);
av2[1]=((C_word*)t0)[2];
av2[2]=((C_word*)((C_word*)t0)[3])[1];
av2[3]=t1;
tp(4,av2);}}

/* doloop569 in k2347 in k2277 in doloop563 in doloop559 in k2237 in k2234 in k2231 in k2228 in k2222 in k2219 in crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_fcall f_2302(C_word t0,C_word t1,C_word t2){
C_word tmp;
C_word t3;
C_word t4;
C_word t5;
C_word t6;
C_word t7;
C_word *a;
loop:
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(29,0,2)))){
C_save_and_reclaim_args((void *)trf_2302,3,t0,t1,t2);}
a=C_alloc(29);
if(C_truep(C_i_nequalp(t2,((C_word*)t0)[2]))){
t3=C_SCHEME_UNDEFINED;
t4=t1;{
C_word av2[2];
av2[0]=t4;
av2[1]=t3;
((C_proc)(void*)(*((C_word*)t4+1)))(2,av2);}}
else{
t3=C_i_nequalp(((C_word*)t0)[3],t2);
if(C_truep(C_i_not(t3))){
t4=(*a=C_CLOSURE_TYPE|6,a[1]=(C_word)f_2325,a[2]=((C_word*)t0)[4],a[3]=t2,a[4]=((C_word*)t0)[5],a[5]=t1,a[6]=((C_word*)t0)[6],tmp=(C_word)a,a+=7,tmp);
C_trace(C_text("crypto-ffi.scm:630: share-x"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[70]);
C_word av2[3];
av2[0]=*((C_word*)lf[70]+1);
av2[1]=t4;
av2[2]=C_i_list_ref(((C_word*)t0)[7],t2);
tp(3,av2);}}
else{
t4=C_s_a_i_plus(&a,2,t2,C_fix(1));
t6=t1;
t7=t4;
t1=t6;
t2=t7;
goto loop;}}}

/* k2323 in doloop569 in k2347 in k2277 in doloop563 in doloop559 in k2237 in k2234 in k2231 in k2228 in k2222 in k2219 in crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 in ... */
static void C_ccall f_2325(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word t5;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(14,c,3)))){
C_save_and_reclaim((void *)f_2325,c,av);}
a=C_alloc(14);
t2=(*a=C_CLOSURE_TYPE|5,a[1]=(C_word)f_2329,a[2]=((C_word*)t0)[2],a[3]=((C_word*)t0)[3],a[4]=((C_word*)t0)[4],a[5]=((C_word*)t0)[5],tmp=(C_word)a,a+=6,tmp);
t3=(*a=C_CLOSURE_TYPE|3,a[1]=(C_word)f_2333,a[2]=t2,a[3]=((C_word*)t0)[2],tmp=(C_word)a,a+=4,tmp);
t4=(*a=C_CLOSURE_TYPE|3,a[1]=(C_word)f_2337,a[2]=t3,a[3]=t1,tmp=(C_word)a,a+=4,tmp);
C_trace(C_text("crypto-ffi.scm:635: gf256-add"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[61]);
C_word *av2;
if(c >= 4) {
  av2=av;
} else {
  av2=C_alloc(4);
}
av2[0]=*((C_word*)lf[61]+1);
av2[1]=t4;
av2[2]=((C_word*)t0)[6];
av2[3]=t1;
tp(4,av2);}}

/* k2327 in k2323 in doloop569 in k2347 in k2277 in doloop563 in doloop559 in k2237 in k2234 in k2231 in k2228 in k2222 in k2219 in crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in ... */
static void C_ccall f_2329(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(29,c,2)))){
C_save_and_reclaim((void *)f_2329,c,av);}
a=C_alloc(29);
t2=C_mutate(((C_word *)((C_word*)t0)[2])+1,t1);
t3=C_s_a_i_plus(&a,2,((C_word*)t0)[3],C_fix(1));
t4=((C_word*)((C_word*)t0)[4])[1];
f_2302(t4,((C_word*)t0)[5],t3);}

/* k2331 in k2323 in doloop569 in k2347 in k2277 in doloop563 in doloop559 in k2237 in k2234 in k2231 in k2228 in k2222 in k2219 in crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in ... */
static void C_ccall f_2333(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,3)))){
C_save_and_reclaim((void *)f_2333,c,av);}
C_trace(C_text("crypto-ffi.scm:633: gf256-mul"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[62]);
C_word *av2;
if(c >= 4) {
  av2=av;
} else {
  av2=C_alloc(4);
}
av2[0]=*((C_word*)lf[62]+1);
av2[1]=((C_word*)t0)[2];
av2[2]=((C_word*)((C_word*)t0)[3])[1];
av2[3]=t1;
tp(4,av2);}}

/* k2335 in k2323 in doloop569 in k2347 in k2277 in doloop563 in doloop559 in k2237 in k2234 in k2231 in k2228 in k2222 in k2219 in crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in ... */
static void C_ccall f_2337(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,3)))){
C_save_and_reclaim((void *)f_2337,c,av);}
C_trace(C_text("crypto-ffi.scm:634: gf256-div"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[63]);
C_word *av2;
if(c >= 4) {
  av2=av;
} else {
  av2=C_alloc(4);
}
av2[0]=*((C_word*)lf[63]+1);
av2[1]=((C_word*)t0)[2];
av2[2]=((C_word*)t0)[3];
av2[3]=t1;
tp(4,av2);}}

/* k2347 in k2277 in doloop563 in doloop559 in k2237 in k2234 in k2231 in k2228 in k2222 in k2219 in crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2349(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word t5;
C_word t6;
C_word t7;
C_word t8;
C_word t9;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(21,c,3)))){
C_save_and_reclaim((void *)f_2349,c,av);}
a=C_alloc(21);
t2=C_i_u8vector_ref(t1,((C_word*)t0)[2]);
t3=C_fix(1);
t4=(*a=C_VECTOR_TYPE|1,a[1]=t3,tmp=(C_word)a,a+=2,tmp);
t5=(*a=C_CLOSURE_TYPE|7,a[1]=(C_word)f_2285,a[2]=((C_word*)t0)[3],a[3]=((C_word*)t0)[4],a[4]=((C_word*)t0)[5],a[5]=((C_word*)t0)[6],a[6]=t2,a[7]=t4,tmp=(C_word)a,a+=8,tmp);
t6=C_SCHEME_UNDEFINED;
t7=(*a=C_VECTOR_TYPE|1,a[1]=t6,tmp=(C_word)a,a+=2,tmp);
t8=C_set_block_item(t7,0,(*a=C_CLOSURE_TYPE|8,a[1]=(C_word)f_2302,a[2]=((C_word*)t0)[7],a[3]=((C_word*)t0)[4],a[4]=t4,a[5]=t7,a[6]=((C_word*)t0)[8],a[7]=((C_word*)t0)[9],a[8]=((C_word)li38),tmp=(C_word)a,a+=9,tmp));
t9=((C_word*)t7)[1];
f_2302(t9,t5,C_fix(0));}

/* k2351 in k2277 in doloop563 in doloop559 in k2237 in k2234 in k2231 in k2228 in k2222 in k2219 in crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2353(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,2)))){
C_save_and_reclaim((void *)f_2353,c,av);}
C_trace(C_text("crypto-ffi.scm:622: srfi-4#blob->u8vector"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[83]);
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[83]+1);
av2[1]=((C_word*)t0)[2];
av2[2]=t1;
tp(3,av2);}}

/* k2363 in k2231 in k2228 in k2222 in k2219 in crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2365(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,2)))){
C_save_and_reclaim((void *)f_2365,c,av);}
C_trace(C_text("crypto-ffi.scm:609: chicken.blob#blob-size"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[11]+1));
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[11]+1);
av2[1]=((C_word*)t0)[2];
av2[2]=t1;
tp(3,av2);}}

/* k2377 in k2222 in k2219 in crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2379(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(6,c,4)))){
C_save_and_reclaim((void *)f_2379,c,av);}
a=C_alloc(6);
t2=(*a=C_CLOSURE_TYPE|5,a[1]=(C_word)f_2382,a[2]=((C_word*)t0)[2],a[3]=t1,a[4]=((C_word*)t0)[3],a[5]=((C_word*)t0)[4],tmp=(C_word)a,a+=6,tmp);
C_trace(C_text("crypto-ffi.scm:605: ##sys#check-output-port"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[95]+1));
C_word *av2;
if(c >= 5) {
  av2=av;
} else {
  av2=C_alloc(5);
}
av2[0]=*((C_word*)lf[95]+1);
av2[1]=t2;
av2[2]=t1;
av2[3]=C_SCHEME_TRUE;
av2[4]=lf[96];
tp(5,av2);}}

/* k2380 in k2377 in k2222 in k2219 in crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2382(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(6,c,4)))){
C_save_and_reclaim((void *)f_2382,c,av);}
a=C_alloc(6);
t2=(*a=C_CLOSURE_TYPE|5,a[1]=(C_word)f_2385,a[2]=((C_word*)t0)[2],a[3]=((C_word*)t0)[3],a[4]=((C_word*)t0)[4],a[5]=((C_word*)t0)[5],tmp=(C_word)a,a+=6,tmp);
C_trace(C_text("crypto-ffi.scm:605: ##sys#print"));
t3=*((C_word*)lf[92]+1);{
C_word *av2;
if(c >= 5) {
  av2=av;
} else {
  av2=C_alloc(5);
}
av2[0]=t3;
av2[1]=t2;
av2[2]=lf[94];
av2[3]=C_SCHEME_FALSE;
av2[4]=((C_word*)t0)[3];
((C_proc)(void*)(*((C_word*)t3+1)))(5,av2);}}

/* k2383 in k2380 in k2377 in k2222 in k2219 in crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2385(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(5,c,4)))){
C_save_and_reclaim((void *)f_2385,c,av);}
a=C_alloc(5);
t2=(*a=C_CLOSURE_TYPE|4,a[1]=(C_word)f_2388,a[2]=((C_word*)t0)[2],a[3]=((C_word*)t0)[3],a[4]=((C_word*)t0)[4],tmp=(C_word)a,a+=5,tmp);
C_trace(C_text("crypto-ffi.scm:605: ##sys#print"));
t3=*((C_word*)lf[92]+1);{
C_word *av2;
if(c >= 5) {
  av2=av;
} else {
  av2=C_alloc(5);
}
av2[0]=t3;
av2[1]=t2;
av2[2]=((C_word*)t0)[5];
av2[3]=C_SCHEME_FALSE;
av2[4]=((C_word*)t0)[3];
((C_proc)(void*)(*((C_word*)t3+1)))(5,av2);}}

/* k2386 in k2383 in k2380 in k2377 in k2222 in k2219 in crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2388(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(5,c,4)))){
C_save_and_reclaim((void *)f_2388,c,av);}
a=C_alloc(5);
t2=(*a=C_CLOSURE_TYPE|4,a[1]=(C_word)f_2391,a[2]=((C_word*)t0)[2],a[3]=((C_word*)t0)[3],a[4]=((C_word*)t0)[4],tmp=(C_word)a,a+=5,tmp);
C_trace(C_text("crypto-ffi.scm:605: ##sys#print"));
t3=*((C_word*)lf[92]+1);{
C_word *av2;
if(c >= 5) {
  av2=av;
} else {
  av2=C_alloc(5);
}
av2[0]=t3;
av2[1]=t2;
av2[2]=lf[93];
av2[3]=C_SCHEME_FALSE;
av2[4]=((C_word*)t0)[3];
((C_proc)(void*)(*((C_word*)t3+1)))(5,av2);}}

/* k2389 in k2386 in k2383 in k2380 in k2377 in k2222 in k2219 in crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2391(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(4,c,4)))){
C_save_and_reclaim((void *)f_2391,c,av);}
a=C_alloc(4);
t2=(*a=C_CLOSURE_TYPE|3,a[1]=(C_word)f_2394,a[2]=((C_word*)t0)[2],a[3]=((C_word*)t0)[3],tmp=(C_word)a,a+=4,tmp);
C_trace(C_text("crypto-ffi.scm:605: ##sys#print"));
t3=*((C_word*)lf[92]+1);{
C_word *av2;
if(c >= 5) {
  av2=av;
} else {
  av2=C_alloc(5);
}
av2[0]=t3;
av2[1]=t2;
av2[2]=((C_word*)t0)[4];
av2[3]=C_SCHEME_FALSE;
av2[4]=((C_word*)t0)[3];
((C_proc)(void*)(*((C_word*)t3+1)))(5,av2);}}

/* k2392 in k2389 in k2386 in k2383 in k2380 in k2377 in k2222 in k2219 in crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2394(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(3,c,2)))){
C_save_and_reclaim((void *)f_2394,c,av);}
a=C_alloc(3);
t2=(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_2397,a[2]=((C_word*)t0)[2],tmp=(C_word)a,a+=3,tmp);
C_trace(C_text("crypto-ffi.scm:605: chicken.base#get-output-string"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[91]);
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[91]+1);
av2[1]=t2;
av2[2]=((C_word*)t0)[3];
tp(3,av2);}}

/* k2395 in k2392 in k2389 in k2386 in k2383 in k2380 in k2377 in k2222 in k2219 in crypto-ffi#shamir-reconstruct in k1832 in k1749 in k1745 in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_2397(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,2)))){
C_save_and_reclaim((void *)f_2397,c,av);}
C_trace(C_text("crypto-ffi.scm:605: chicken.base#error"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[39]+1));
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[39]+1);
av2[1]=((C_word*)t0)[2];
av2[2]=t1;
tp(3,av2);}}

/* k865 */
static void C_ccall f_867(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(3,c,2)))){
C_save_and_reclaim((void *)f_867,c,av);}
a=C_alloc(3);
t2=(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_870,a[2]=((C_word*)t0)[2],tmp=(C_word)a,a+=3,tmp);{
C_word *av2=av;
av2[0]=C_SCHEME_UNDEFINED;
av2[1]=t2;
C_eval_toplevel(2,av2);}}

/* k868 in k865 */
static void C_ccall f_870(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(11,c,2)))){
C_save_and_reclaim((void *)f_870,c,av);}
a=C_alloc(11);
t2=C_a_i_provide(&a,1,lf[0]);
t3=(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_873,a[2]=((C_word*)t0)[2],tmp=(C_word)a,a+=3,tmp);{
C_word *av2=av;
av2[0]=C_SCHEME_UNDEFINED;
av2[1]=t3;
C_extras_toplevel(2,av2);}}

/* k871 in k868 in k865 */
static void C_ccall f_873(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(3,c,2)))){
C_save_and_reclaim((void *)f_873,c,av);}
a=C_alloc(3);
t2=(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_876,a[2]=((C_word*)t0)[2],tmp=(C_word)a,a+=3,tmp);{
C_word *av2=av;
av2[0]=C_SCHEME_UNDEFINED;
av2[1]=t2;
C_lolevel_toplevel(2,av2);}}

/* k874 in k871 in k868 in k865 */
static void C_ccall f_876(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(3,c,4)))){
C_save_and_reclaim((void *)f_876,c,av);}
a=C_alloc(3);
t2=(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_879,a[2]=((C_word*)t0)[2],tmp=(C_word)a,a+=3,tmp);
C_trace(C_text("crypto-ffi.scm:66: chicken.load#load-extension"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[99]);
C_word *av2;
if(c >= 5) {
  av2=av;
} else {
  av2=C_alloc(5);
}
av2[0]=*((C_word*)lf[99]+1);
av2[1]=t2;
av2[2]=lf[100];
av2[3]=C_SCHEME_TRUE;
av2[4]=C_SCHEME_FALSE;
tp(5,av2);}}

/* k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_879(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(3,c,2)))){
C_save_and_reclaim((void *)f_879,c,av);}
a=C_alloc(3);
t2=(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_882,a[2]=((C_word*)t0)[2],tmp=(C_word)a,a+=3,tmp);{
C_word *av2=av;
av2[0]=C_SCHEME_UNDEFINED;
av2[1]=t2;
C_srfi_2d4_toplevel(2,av2);}}

/* k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_882(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word t5;
C_word t6;
C_word t7;
C_word t8;
C_word t9;
C_word t10;
C_word t11;
C_word t12;
C_word t13;
C_word t14;
C_word t15;
C_word t16;
C_word t17;
C_word t18;
C_word t19;
C_word t20;
C_word t21;
C_word t22;
C_word t23;
C_word t24;
C_word t25;
C_word t26;
C_word t27;
C_word t28;
C_word t29;
C_word t30;
C_word t31;
C_word t32;
C_word t33;
C_word t34;
C_word t35;
C_word t36;
C_word t37;
C_word t38;
C_word t39;
C_word t40;
C_word t41;
C_word t42;
C_word t43;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(63,c,5)))){
C_save_and_reclaim((void *)f_882,c,av);}
a=C_alloc(63);
t2=C_set_block_item(lf[1] /* crypto-ffi#crypto-sign-publickeybytes */,0,C_fix(32));
t3=C_set_block_item(lf[2] /* crypto-ffi#crypto-sign-secretkeybytes */,0,C_fix(64));
t4=C_set_block_item(lf[3] /* crypto-ffi#crypto-sign-bytes */,0,C_fix(64));
t5=C_mutate((C_word*)lf[4]+1 /* (set! crypto-ffi#sodium-init ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_889,a[2]=((C_word)li0),tmp=(C_word)a,a+=3,tmp));
t6=C_mutate((C_word*)lf[5]+1 /* (set! crypto-ffi#ed25519-keypair! ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_892,a[2]=((C_word)li1),tmp=(C_word)a,a+=3,tmp));
t7=C_mutate((C_word*)lf[6]+1 /* (set! crypto-ffi#ed25519-keypair ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_909,a[2]=((C_word)li2),tmp=(C_word)a,a+=3,tmp));
t8=C_mutate((C_word*)lf[8]+1 /* (set! crypto-ffi#ed25519-secret-to-public ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_924,a[2]=((C_word)li4),tmp=(C_word)a,a+=3,tmp));
t9=C_mutate((C_word*)lf[10]+1 /* (set! crypto-ffi#ed25519-sign ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_966,a[2]=((C_word)li5),tmp=(C_word)a,a+=3,tmp));
t10=C_mutate((C_word*)lf[13]+1 /* (set! crypto-ffi#ed25519-verify ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1026,a[2]=((C_word)li6),tmp=(C_word)a,a+=3,tmp));
t11=C_mutate((C_word*)lf[14]+1 /* (set! crypto-ffi#sha256-hash ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1076,a[2]=((C_word)li7),tmp=(C_word)a,a+=3,tmp));
t12=C_mutate((C_word*)lf[15]+1 /* (set! crypto-ffi#sha512-hash ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1119,a[2]=((C_word)li8),tmp=(C_word)a,a+=3,tmp));
t13=C_set_block_item(lf[16] /* crypto-ffi#crypto-generichash-bytes */,0,C_fix(32));
t14=C_mutate((C_word*)lf[17]+1 /* (set! crypto-ffi#blake2b-hash ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1163,a[2]=((C_word)li9),tmp=(C_word)a,a+=3,tmp));
t15=C_set_block_item(lf[18] /* crypto-ffi#secretbox-keybytes */,0,C_fix(32));
t16=C_set_block_item(lf[19] /* crypto-ffi#secretbox-noncebytes */,0,C_fix(24));
t17=C_set_block_item(lf[20] /* crypto-ffi#x25519-publickeybytes */,0,C_fix(32));
t18=C_set_block_item(lf[21] /* crypto-ffi#x25519-secretkeybytes */,0,C_fix(32));
t19=C_mutate((C_word*)lf[22]+1 /* (set! crypto-ffi#random-bytes ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1230,a[2]=((C_word)li10),tmp=(C_word)a,a+=3,tmp));
t20=C_mutate((C_word*)lf[23]+1 /* (set! crypto-ffi#random-u8 ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1253,a[2]=((C_word)li11),tmp=(C_word)a,a+=3,tmp));
t21=C_mutate((C_word*)lf[24]+1 /* (set! crypto-ffi#random-u32 ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1286,a[2]=((C_word)li12),tmp=(C_word)a,a+=3,tmp));
t22=C_mutate((C_word*)lf[25]+1 /* (set! crypto-ffi#random-uniform ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1294,a[2]=((C_word)li13),tmp=(C_word)a,a+=3,tmp));
t23=C_mutate((C_word*)lf[26]+1 /* (set! crypto-ffi#entropy-status ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1306,a[2]=((C_word)li14),tmp=(C_word)a,a+=3,tmp));
t24=C_mutate((C_word*)lf[37]+1 /* (set! crypto-ffi#memzero! ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1346,a[2]=((C_word)li15),tmp=(C_word)a,a+=3,tmp));
t25=C_mutate((C_word*)lf[38]+1 /* (set! crypto-ffi#argon2id-hash ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1370,a[2]=((C_word)li16),tmp=(C_word)a,a+=3,tmp));
t26=C_mutate((C_word*)lf[41]+1 /* (set! crypto-ffi#secretbox-encrypt ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1448,a[2]=((C_word)li17),tmp=(C_word)a,a+=3,tmp));
t27=C_mutate((C_word*)lf[43]+1 /* (set! crypto-ffi#secretbox-decrypt ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1508,a[2]=((C_word)li18),tmp=(C_word)a,a+=3,tmp));
t28=C_mutate((C_word*)lf[44]+1 /* (set! crypto-ffi#seal ...) */,C_fast_retrieve(lf[41]));
t29=C_mutate((C_word*)lf[45]+1 /* (set! crypto-ffi#unseal ...) */,C_fast_retrieve(lf[43]));
t30=C_mutate((C_word*)lf[46]+1 /* (set! crypto-ffi#encipher ...) */,C_fast_retrieve(lf[41]));
t31=C_mutate((C_word*)lf[47]+1 /* (set! crypto-ffi#decipher ...) */,C_fast_retrieve(lf[43]));
t32=C_mutate((C_word*)lf[48]+1 /* (set! crypto-ffi#shroud ...) */,C_fast_retrieve(lf[41]));
t33=C_mutate((C_word*)lf[49]+1 /* (set! crypto-ffi#unshroud ...) */,C_fast_retrieve(lf[43]));
t34=C_mutate((C_word*)lf[50]+1 /* (set! crypto-ffi#ward ...) */,C_fast_retrieve(lf[41]));
t35=C_mutate((C_word*)lf[51]+1 /* (set! crypto-ffi#unward ...) */,C_fast_retrieve(lf[43]));
t36=C_mutate((C_word*)lf[52]+1 /* (set! crypto-ffi#veil ...) */,C_fast_retrieve(lf[41]));
t37=C_mutate((C_word*)lf[53]+1 /* (set! crypto-ffi#unveil ...) */,C_fast_retrieve(lf[43]));
t38=C_mutate((C_word*)lf[54]+1 /* (set! crypto-ffi#entrust ...) */,C_fast_retrieve(lf[41]));
t39=C_mutate((C_word*)lf[55]+1 /* (set! crypto-ffi#recover ...) */,C_fast_retrieve(lf[43]));
t40=C_mutate((C_word*)lf[56]+1 /* (set! crypto-ffi#x25519-keypair ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1577,a[2]=((C_word)li19),tmp=(C_word)a,a+=3,tmp));
t41=C_mutate((C_word*)lf[57]+1 /* (set! crypto-ffi#x25519-scalarmult ...) */,(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1608,a[2]=((C_word)li20),tmp=(C_word)a,a+=3,tmp));
t42=(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_1747,a[2]=((C_word*)t0)[2],tmp=(C_word)a,a+=3,tmp);
C_trace(C_text("crypto-ffi.scm:463: srfi-4#make-u8vector"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[82]);
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[82]+1);
av2[1]=t42;
av2[2]=C_fix(512);
tp(3,av2);}}

/* crypto-ffi#sodium-init in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_889(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word *a;
if(c!=2) C_bad_argc_2(c,2,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,1)))){
C_save_and_reclaim((void *)f_889,c,av);}
t2=t1;{
C_word *av2=av;
av2[0]=t2;
av2[1]=stub26(C_SCHEME_UNDEFINED);
((C_proc)(void*)(*((C_word*)t2+1)))(2,av2);}}

/* crypto-ffi#ed25519-keypair! in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_892(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2=av[2];
C_word t3=av[3];
C_word t4;
C_word t5;
C_word *a;
if(c!=4) C_bad_argc_2(c,4,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(0,c,1)))){
C_save_and_reclaim((void *)f_892,c,av);}
t4=(C_truep(t2)?C_i_foreign_block_argumentp(t2):C_SCHEME_FALSE);
t5=t1;{
C_word *av2=av;
av2[0]=t5;
av2[1]=(C_truep(t3)?stub31(C_SCHEME_UNDEFINED,t4,C_i_foreign_block_argumentp(t3)):stub31(C_SCHEME_UNDEFINED,t4,C_SCHEME_FALSE));
((C_proc)(void*)(*((C_word*)t5+1)))(2,av2);}}

/* crypto-ffi#ed25519-keypair in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_909(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
if(c!=2) C_bad_argc_2(c,2,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(3,c,2)))){
C_save_and_reclaim((void *)f_909,c,av);}
a=C_alloc(3);
t2=(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_913,a[2]=t1,tmp=(C_word)a,a+=3,tmp);
C_trace(C_text("crypto-ffi.scm:105: chicken.blob#make-blob"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[7]);
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[7]+1);
av2[1]=t2;
av2[2]=C_fast_retrieve(lf[1]);
tp(3,av2);}}

/* k911 in crypto-ffi#ed25519-keypair in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_913(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(4,c,2)))){
C_save_and_reclaim((void *)f_913,c,av);}
a=C_alloc(4);
t2=(*a=C_CLOSURE_TYPE|3,a[1]=(C_word)f_916,a[2]=((C_word*)t0)[2],a[3]=t1,tmp=(C_word)a,a+=4,tmp);
C_trace(C_text("crypto-ffi.scm:106: chicken.blob#make-blob"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[7]);
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[7]+1);
av2[1]=t2;
av2[2]=C_fast_retrieve(lf[2]);
tp(3,av2);}}

/* k914 in k911 in crypto-ffi#ed25519-keypair in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_916(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(5,c,3)))){
C_save_and_reclaim((void *)f_916,c,av);}
a=C_alloc(5);
t2=(*a=C_CLOSURE_TYPE|4,a[1]=(C_word)f_919,a[2]=((C_word*)t0)[2],a[3]=((C_word*)t0)[3],a[4]=t1,tmp=(C_word)a,a+=5,tmp);
C_trace(C_text("crypto-ffi.scm:107: ed25519-keypair!"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[5]);
C_word *av2;
if(c >= 4) {
  av2=av;
} else {
  av2=C_alloc(4);
}
av2[0]=*((C_word*)lf[5]+1);
av2[1]=t2;
av2[2]=((C_word*)t0)[3];
av2[3]=t1;
tp(4,av2);}}

/* k917 in k914 in k911 in crypto-ffi#ed25519-keypair in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_919(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(6,c,1)))){
C_save_and_reclaim((void *)f_919,c,av);}
a=C_alloc(6);
t2=((C_word*)t0)[2];{
C_word *av2=av;
av2[0]=t2;
av2[1]=C_a_i_list2(&a,2,((C_word*)t0)[3],((C_word*)t0)[4]);
((C_proc)(void*)(*((C_word*)t2+1)))(2,av2);}}

/* crypto-ffi#ed25519-secret-to-public in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_924(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2=av[2];
C_word t3;
C_word t4;
C_word *a;
if(c!=3) C_bad_argc_2(c,3,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(4,c,2)))){
C_save_and_reclaim((void *)f_924,c,av);}
a=C_alloc(4);
t3=(*a=C_CLOSURE_TYPE|3,a[1]=(C_word)f_928,a[2]=t1,a[3]=t2,tmp=(C_word)a,a+=4,tmp);
C_trace(C_text("crypto-ffi.scm:115: chicken.blob#make-blob"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[7]);
C_word *av2=av;
av2[0]=*((C_word*)lf[7]+1);
av2[1]=t3;
av2[2]=C_fast_retrieve(lf[1]);
tp(3,av2);}}

/* k926 in crypto-ffi#ed25519-secret-to-public in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_928(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(4,c,2)))){
C_save_and_reclaim((void *)f_928,c,av);}
a=C_alloc(4);
t2=(*a=C_CLOSURE_TYPE|3,a[1]=(C_word)f_931,a[2]=t1,a[3]=((C_word*)t0)[2],tmp=(C_word)a,a+=4,tmp);
C_trace(C_text("crypto-ffi.scm:116: srfi-4#blob->u8vector/shared"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[9]+1));
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[9]+1);
av2[1]=t2;
av2[2]=((C_word*)t0)[3];
tp(3,av2);}}

/* k929 in k926 in crypto-ffi#ed25519-secret-to-public in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_931(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(5,c,2)))){
C_save_and_reclaim((void *)f_931,c,av);}
a=C_alloc(5);
t2=(*a=C_CLOSURE_TYPE|4,a[1]=(C_word)f_934,a[2]=((C_word*)t0)[2],a[3]=t1,a[4]=((C_word*)t0)[3],tmp=(C_word)a,a+=5,tmp);
C_trace(C_text("crypto-ffi.scm:117: srfi-4#blob->u8vector/shared"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[9]+1));
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[9]+1);
av2[1]=t2;
av2[2]=((C_word*)t0)[2];
tp(3,av2);}}

/* k932 in k929 in k926 in crypto-ffi#ed25519-secret-to-public in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_934(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word t4;
C_word t5;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(9,c,3)))){
C_save_and_reclaim((void *)f_934,c,av);}
a=C_alloc(9);
t2=C_SCHEME_UNDEFINED;
t3=(*a=C_VECTOR_TYPE|1,a[1]=t2,tmp=(C_word)a,a+=2,tmp);
t4=C_set_block_item(t3,0,(*a=C_CLOSURE_TYPE|6,a[1]=(C_word)f_939,a[2]=((C_word*)t0)[2],a[3]=((C_word*)t0)[3],a[4]=t1,a[5]=t3,a[6]=((C_word)li3),tmp=(C_word)a,a+=7,tmp));
t5=((C_word*)t3)[1];
f_939(t5,((C_word*)t0)[4],C_fix(0));}

/* doloop48 in k932 in k929 in k926 in crypto-ffi#ed25519-secret-to-public in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_fcall f_939(C_word t0,C_word t1,C_word t2){
C_word tmp;
C_word t3;
C_word t4;
C_word t5;
C_word t6;
C_word t7;
C_word t8;
C_word t9;
C_word *a;
loop:
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(58,0,2)))){
C_save_and_reclaim_args((void *)trf_939,3,t0,t1,t2);}
a=C_alloc(58);
if(C_truep(C_i_nequalp(t2,C_fast_retrieve(lf[1])))){
t3=t1;{
C_word av2[2];
av2[0]=t3;
av2[1]=((C_word*)t0)[2];
((C_proc)(void*)(*((C_word*)t3+1)))(2,av2);}}
else{
t3=C_s_a_i_plus(&a,2,t2,C_fix(32));
t4=C_i_u8vector_ref(((C_word*)t0)[3],t3);
t5=C_i_u8vector_set(((C_word*)t0)[4],t2,t4);
t6=C_s_a_i_plus(&a,2,t2,C_fix(1));
t8=t1;
t9=t6;
t1=t8;
t2=t9;
goto loop;}}

/* crypto-ffi#ed25519-sign in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_966(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2=av[2];
C_word t3=av[3];
C_word t4;
C_word t5;
C_word *a;
if(c!=4) C_bad_argc_2(c,4,t0);
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(4,c,2)))){
C_save_and_reclaim((void *)f_966,c,av);}
a=C_alloc(4);
t4=(*a=C_CLOSURE_TYPE|3,a[1]=(C_word)f_970,a[2]=t2,a[3]=t1,tmp=(C_word)a,a+=4,tmp);
if(C_truep(C_i_stringp(t3))){
C_trace(C_text("crypto-ffi.scm:129: chicken.blob#string->blob"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[12]);
C_word *av2=av;
av2[0]=*((C_word*)lf[12]+1);
av2[1]=t4;
av2[2]=t3;
tp(3,av2);}}
else{
t5=t4;{
C_word *av2=av;
av2[0]=t5;
av2[1]=t3;
f_970(2,av2);}}}

/* k968 in crypto-ffi#ed25519-sign in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_970(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(5,c,2)))){
C_save_and_reclaim((void *)f_970,c,av);}
a=C_alloc(5);
t2=(*a=C_CLOSURE_TYPE|4,a[1]=(C_word)f_973,a[2]=t1,a[3]=((C_word*)t0)[2],a[4]=((C_word*)t0)[3],tmp=(C_word)a,a+=5,tmp);
C_trace(C_text("crypto-ffi.scm:131: chicken.blob#make-blob"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[7]);
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[7]+1);
av2[1]=t2;
av2[2]=C_fast_retrieve(lf[3]);
tp(3,av2);}}

/* k971 in k968 in crypto-ffi#ed25519-sign in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_973(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(6,c,2)))){
C_save_and_reclaim((void *)f_973,c,av);}
a=C_alloc(6);
t2=(*a=C_CLOSURE_TYPE|5,a[1]=(C_word)f_976,a[2]=t1,a[3]=((C_word*)t0)[2],a[4]=((C_word*)t0)[3],a[5]=((C_word*)t0)[4],tmp=(C_word)a,a+=6,tmp);
C_trace(C_text("crypto-ffi.scm:132: chicken.blob#make-blob"));
{C_proc tp=(C_proc)C_fast_retrieve_symbol_proc(lf[7]);
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[7]+1);
av2[1]=t2;
av2[2]=C_fix(8);
tp(3,av2);}}

/* k974 in k971 in k968 in crypto-ffi#ed25519-sign in k880 in k877 in k874 in k871 in k868 in k865 */
static void C_ccall f_976(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
C_check_for_interrupt;
if(C_unlikely(!C_demand(C_calculate_demand(7,c,2)))){
C_save_and_reclaim((void *)f_976,c,av);}
a=C_alloc(7);
t2=(*a=C_CLOSURE_TYPE|6,a[1]=(C_word)f_1018,a[2]=((C_word*)t0)[2],a[3]=t1,a[4]=((C_word*)t0)[3],a[5]=((C_word*)t0)[4],a[6]=((C_word*)t0)[5],tmp=(C_word)a,a+=7,tmp);
C_trace(C_text("crypto-ffi.scm:139: chicken.blob#blob-size"));
{C_proc tp=(C_proc)C_fast_retrieve_proc(*((C_word*)lf[11]+1));
C_word *av2;
if(c >= 3) {
  av2=av;
} else {
  av2=C_alloc(3);
}
av2[0]=*((C_word*)lf[11]+1);
av2[1]=t2;
av2[2]=((C_word*)t0)[3];
tp(3,av2);}}

/* toplevel */
static C_TLS int toplevel_initialized=0;
C_main_entry_point

void C_ccall C_toplevel(C_word c,C_word *av){
C_word tmp;
C_word t0=av[0];
C_word t1=av[1];
C_word t2;
C_word t3;
C_word *a;
if(toplevel_initialized) {C_kontinue(t1,C_SCHEME_UNDEFINED);}
else C_toplevel_entry(C_text("toplevel"));
C_check_nursery_minimum(C_calculate_demand(3,c,2));
if(C_unlikely(!C_demand(C_calculate_demand(3,c,2)))){
C_save_and_reclaim((void*)C_toplevel,c,av);}
toplevel_initialized=1;
if(C_unlikely(!C_demand_2(595))){
C_save(t1);
C_rereclaim2(595*sizeof(C_word),1);
t1=C_restore;}
a=C_alloc(3);
C_initialize_lf(lf,101);
lf[0]=C_h_intern(&lf[0],11, C_text("crypto-ffi#"));
lf[1]=C_h_intern(&lf[1],37, C_text("crypto-ffi#crypto-sign-publickeybytes"));
lf[2]=C_h_intern(&lf[2],37, C_text("crypto-ffi#crypto-sign-secretkeybytes"));
lf[3]=C_h_intern(&lf[3],28, C_text("crypto-ffi#crypto-sign-bytes"));
lf[4]=C_h_intern(&lf[4],22, C_text("crypto-ffi#sodium-init"));
lf[5]=C_h_intern(&lf[5],27, C_text("crypto-ffi#ed25519-keypair!"));
lf[6]=C_h_intern(&lf[6],26, C_text("crypto-ffi#ed25519-keypair"));
lf[7]=C_h_intern(&lf[7],22, C_text("chicken.blob#make-blob"));
lf[8]=C_h_intern(&lf[8],35, C_text("crypto-ffi#ed25519-secret-to-public"));
lf[9]=C_h_intern(&lf[9],28, C_text("srfi-4#blob->u8vector/shared"));
lf[10]=C_h_intern(&lf[10],23, C_text("crypto-ffi#ed25519-sign"));
lf[11]=C_h_intern(&lf[11],22, C_text("chicken.blob#blob-size"));
lf[12]=C_h_intern(&lf[12],25, C_text("chicken.blob#string->blob"));
lf[13]=C_h_intern(&lf[13],25, C_text("crypto-ffi#ed25519-verify"));
lf[14]=C_h_intern(&lf[14],22, C_text("crypto-ffi#sha256-hash"));
lf[15]=C_h_intern(&lf[15],22, C_text("crypto-ffi#sha512-hash"));
lf[16]=C_h_intern(&lf[16],35, C_text("crypto-ffi#crypto-generichash-bytes"));
lf[17]=C_h_intern(&lf[17],23, C_text("crypto-ffi#blake2b-hash"));
lf[18]=C_h_intern(&lf[18],29, C_text("crypto-ffi#secretbox-keybytes"));
lf[19]=C_h_intern(&lf[19],31, C_text("crypto-ffi#secretbox-noncebytes"));
lf[20]=C_h_intern(&lf[20],32, C_text("crypto-ffi#x25519-publickeybytes"));
lf[21]=C_h_intern(&lf[21],32, C_text("crypto-ffi#x25519-secretkeybytes"));
lf[22]=C_h_intern(&lf[22],23, C_text("crypto-ffi#random-bytes"));
lf[23]=C_h_intern(&lf[23],20, C_text("crypto-ffi#random-u8"));
lf[24]=C_h_intern(&lf[24],21, C_text("crypto-ffi#random-u32"));
lf[25]=C_h_intern(&lf[25],25, C_text("crypto-ffi#random-uniform"));
lf[26]=C_h_intern(&lf[26],25, C_text("crypto-ffi#entropy-status"));
lf[27]=C_h_intern(&lf[27],14, C_text("implementation"));
lf[28]=C_decode_literal(C_heaptop,C_text("\376B\000\000\011sysrandom"));
lf[29]=C_h_intern(&lf[29],6, C_text("source"));
lf[30]=C_decode_literal(C_heaptop,C_text("\376B\000\000\014/dev/urandom"));
lf[31]=C_h_intern(&lf[31],6, C_text("status"));
lf[32]=C_h_intern(&lf[32],2, C_text("ok"));
lf[33]=C_decode_literal(C_heaptop,C_text("\376B\000\000\010internal"));
lf[34]=C_decode_literal(C_heaptop,C_text("\376B\000\000\021ChaCha20 (seeded)"));
lf[35]=C_decode_literal(C_heaptop,C_text("\376B\000\000\007unknown"));
lf[36]=C_h_intern(&lf[36],19, C_text("##sys#peek-c-string"));
lf[37]=C_h_intern(&lf[37],19, C_text("crypto-ffi#memzero!"));
lf[38]=C_h_intern(&lf[38],24, C_text("crypto-ffi#argon2id-hash"));
lf[39]=C_h_intern(&lf[39],18, C_text("chicken.base#error"));
lf[40]=C_decode_literal(C_heaptop,C_text("\376B\000\000\024argon2id-hash failed"));
lf[41]=C_h_intern(&lf[41],28, C_text("crypto-ffi#secretbox-encrypt"));
lf[42]=C_decode_literal(C_heaptop,C_text("\376B\000\000\030secretbox-encrypt failed"));
lf[43]=C_h_intern(&lf[43],28, C_text("crypto-ffi#secretbox-decrypt"));
lf[44]=C_h_intern(&lf[44],15, C_text("crypto-ffi#seal"));
lf[45]=C_h_intern(&lf[45],17, C_text("crypto-ffi#unseal"));
lf[46]=C_h_intern(&lf[46],19, C_text("crypto-ffi#encipher"));
lf[47]=C_h_intern(&lf[47],19, C_text("crypto-ffi#decipher"));
lf[48]=C_h_intern(&lf[48],17, C_text("crypto-ffi#shroud"));
lf[49]=C_h_intern(&lf[49],19, C_text("crypto-ffi#unshroud"));
lf[50]=C_h_intern(&lf[50],15, C_text("crypto-ffi#ward"));
lf[51]=C_h_intern(&lf[51],17, C_text("crypto-ffi#unward"));
lf[52]=C_h_intern(&lf[52],15, C_text("crypto-ffi#veil"));
lf[53]=C_h_intern(&lf[53],17, C_text("crypto-ffi#unveil"));
lf[54]=C_h_intern(&lf[54],18, C_text("crypto-ffi#entrust"));
lf[55]=C_h_intern(&lf[55],18, C_text("crypto-ffi#recover"));
lf[56]=C_h_intern(&lf[56],25, C_text("crypto-ffi#x25519-keypair"));
lf[57]=C_h_intern(&lf[57],28, C_text("crypto-ffi#x25519-scalarmult"));
lf[58]=C_decode_literal(C_heaptop,C_text("\376B\000\000\030x25519-scalarmult failed"));
lf[61]=C_h_intern(&lf[61],20, C_text("crypto-ffi#gf256-add"));
lf[62]=C_h_intern(&lf[62],20, C_text("crypto-ffi#gf256-mul"));
lf[63]=C_h_intern(&lf[63],20, C_text("crypto-ffi#gf256-div"));
lf[64]=C_h_intern(&lf[64],24, C_text("crypto-ffi#shamir-share\077"));
lf[65]=C_h_intern(&lf[65],25, C_text("crypto-ffi#<shamir-share>"));
lf[66]=C_h_intern(&lf[66],19, C_text("crypto-ffi#share-id"));
lf[67]=C_h_intern(&lf[67],8, C_text("share-id"));
lf[68]=C_h_intern(&lf[68],26, C_text("crypto-ffi#share-threshold"));
lf[69]=C_h_intern(&lf[69],15, C_text("share-threshold"));
lf[70]=C_h_intern(&lf[70],18, C_text("crypto-ffi#share-x"));
lf[71]=C_h_intern(&lf[71],7, C_text("share-x"));
lf[72]=C_h_intern(&lf[72],18, C_text("crypto-ffi#share-y"));
lf[73]=C_h_intern(&lf[73],7, C_text("share-y"));
lf[74]=C_h_intern(&lf[74],23, C_text("crypto-ffi#shamir-split"));
lf[75]=C_h_intern(&lf[75],19, C_text("scheme#vector->list"));
lf[76]=C_h_intern(&lf[76],21, C_text("srfi-4#u8vector->blob"));
lf[77]=C_h_intern(&lf[77],21, C_text("scheme#string->symbol"));
lf[78]=C_h_intern(&lf[78],20, C_text("scheme#string-append"));
lf[79]=C_decode_literal(C_heaptop,C_text("\376B\000\000\006share-"));
lf[80]=C_h_intern(&lf[80],21, C_text("scheme#number->string"));
lf[81]=C_h_intern(&lf[81],18, C_text("scheme#make-vector"));
lf[82]=C_h_intern(&lf[82],20, C_text("srfi-4#make-u8vector"));
lf[83]=C_h_intern(&lf[83],21, C_text("srfi-4#blob->u8vector"));
lf[84]=C_decode_literal(C_heaptop,C_text("\376B\000\000\025Threshold must be > 1"));
lf[85]=C_decode_literal(C_heaptop,C_text("\376B\000\000!Threshold must be <= total shares"));
lf[86]=C_h_intern(&lf[86],17, C_text("##sys#get-keyword"));
lf[87]=C_h_intern_kw(&lf[87],5, C_text("total"));
lf[88]=C_h_intern_kw(&lf[88],9, C_text("threshold"));
lf[89]=C_h_intern(&lf[89],29, C_text("crypto-ffi#shamir-reconstruct"));
lf[90]=C_h_intern(&lf[90],11, C_text("srfi-1#take"));
lf[91]=C_h_intern(&lf[91],30, C_text("chicken.base#get-output-string"));
lf[92]=C_h_intern(&lf[92],11, C_text("##sys#print"));
lf[93]=C_decode_literal(C_heaptop,C_text("\376B\000\000\015 shares, got "));
lf[94]=C_decode_literal(C_heaptop,C_text("\376B\000\000\016Need at least "));
lf[95]=C_h_intern(&lf[95],23, C_text("##sys#check-output-port"));
lf[96]=C_h_intern(&lf[96],6, C_text("format"));
lf[97]=C_h_intern(&lf[97],31, C_text("chicken.base#open-output-string"));
lf[98]=C_decode_literal(C_heaptop,C_text("\376B\000\000\027Need at least one share"));
lf[99]=C_h_intern(&lf[99],27, C_text("chicken.load#load-extension"));
lf[100]=C_h_intern(&lf[100],6, C_text("srfi-1"));
C_register_lf2(lf,101,create_ptable());{}
t2=(*a=C_CLOSURE_TYPE|2,a[1]=(C_word)f_867,a[2]=t1,tmp=(C_word)a,a+=3,tmp);{
C_word *av2=av;
av2[0]=C_SCHEME_UNDEFINED;
av2[1]=t2;
C_library_toplevel(2,av2);}}

#ifdef C_ENABLE_PTABLES
static C_PTABLE_ENTRY ptable[141] = {
{C_text("f_1018:crypto_2dffi_2escm"),(void*)f_1018},
{C_text("f_1026:crypto_2dffi_2escm"),(void*)f_1026},
{C_text("f_1030:crypto_2dffi_2escm"),(void*)f_1030},
{C_text("f_1068:crypto_2dffi_2escm"),(void*)f_1068},
{C_text("f_1076:crypto_2dffi_2escm"),(void*)f_1076},
{C_text("f_1080:crypto_2dffi_2escm"),(void*)f_1080},
{C_text("f_1083:crypto_2dffi_2escm"),(void*)f_1083},
{C_text("f_1111:crypto_2dffi_2escm"),(void*)f_1111},
{C_text("f_1119:crypto_2dffi_2escm"),(void*)f_1119},
{C_text("f_1123:crypto_2dffi_2escm"),(void*)f_1123},
{C_text("f_1126:crypto_2dffi_2escm"),(void*)f_1126},
{C_text("f_1154:crypto_2dffi_2escm"),(void*)f_1154},
{C_text("f_1163:crypto_2dffi_2escm"),(void*)f_1163},
{C_text("f_1167:crypto_2dffi_2escm"),(void*)f_1167},
{C_text("f_1170:crypto_2dffi_2escm"),(void*)f_1170},
{C_text("f_1215:crypto_2dffi_2escm"),(void*)f_1215},
{C_text("f_1230:crypto_2dffi_2escm"),(void*)f_1230},
{C_text("f_1234:crypto_2dffi_2escm"),(void*)f_1234},
{C_text("f_1253:crypto_2dffi_2escm"),(void*)f_1253},
{C_text("f_1257:crypto_2dffi_2escm"),(void*)f_1257},
{C_text("f_1277:crypto_2dffi_2escm"),(void*)f_1277},
{C_text("f_1284:crypto_2dffi_2escm"),(void*)f_1284},
{C_text("f_1286:crypto_2dffi_2escm"),(void*)f_1286},
{C_text("f_1294:crypto_2dffi_2escm"),(void*)f_1294},
{C_text("f_1306:crypto_2dffi_2escm"),(void*)f_1306},
{C_text("f_1316:crypto_2dffi_2escm"),(void*)f_1316},
{C_text("f_1346:crypto_2dffi_2escm"),(void*)f_1346},
{C_text("f_1368:crypto_2dffi_2escm"),(void*)f_1368},
{C_text("f_1370:crypto_2dffi_2escm"),(void*)f_1370},
{C_text("f_1374:crypto_2dffi_2escm"),(void*)f_1374},
{C_text("f_1377:crypto_2dffi_2escm"),(void*)f_1377},
{C_text("f_1440:crypto_2dffi_2escm"),(void*)f_1440},
{C_text("f_1448:crypto_2dffi_2escm"),(void*)f_1448},
{C_text("f_1452:crypto_2dffi_2escm"),(void*)f_1452},
{C_text("f_1455:crypto_2dffi_2escm"),(void*)f_1455},
{C_text("f_1508:crypto_2dffi_2escm"),(void*)f_1508},
{C_text("f_1512:crypto_2dffi_2escm"),(void*)f_1512},
{C_text("f_1515:crypto_2dffi_2escm"),(void*)f_1515},
{C_text("f_1577:crypto_2dffi_2escm"),(void*)f_1577},
{C_text("f_1581:crypto_2dffi_2escm"),(void*)f_1581},
{C_text("f_1584:crypto_2dffi_2escm"),(void*)f_1584},
{C_text("f_1608:crypto_2dffi_2escm"),(void*)f_1608},
{C_text("f_1612:crypto_2dffi_2escm"),(void*)f_1612},
{C_text("f_1747:crypto_2dffi_2escm"),(void*)f_1747},
{C_text("f_1751:crypto_2dffi_2escm"),(void*)f_1751},
{C_text("f_1757:crypto_2dffi_2escm"),(void*)f_1757},
{C_text("f_1762:crypto_2dffi_2escm"),(void*)f_1762},
{C_text("f_1789:crypto_2dffi_2escm"),(void*)f_1789},
{C_text("f_1834:crypto_2dffi_2escm"),(void*)f_1834},
{C_text("f_1836:crypto_2dffi_2escm"),(void*)f_1836},
{C_text("f_1842:crypto_2dffi_2escm"),(void*)f_1842},
{C_text("f_1876:crypto_2dffi_2escm"),(void*)f_1876},
{C_text("f_1918:crypto_2dffi_2escm"),(void*)f_1918},
{C_text("f_1936:crypto_2dffi_2escm"),(void*)f_1936},
{C_text("f_1944:crypto_2dffi_2escm"),(void*)f_1944},
{C_text("f_1957:crypto_2dffi_2escm"),(void*)f_1957},
{C_text("f_1963:crypto_2dffi_2escm"),(void*)f_1963},
{C_text("f_1972:crypto_2dffi_2escm"),(void*)f_1972},
{C_text("f_1981:crypto_2dffi_2escm"),(void*)f_1981},
{C_text("f_1990:crypto_2dffi_2escm"),(void*)f_1990},
{C_text("f_1999:crypto_2dffi_2escm"),(void*)f_1999},
{C_text("f_2003:crypto_2dffi_2escm"),(void*)f_2003},
{C_text("f_2006:crypto_2dffi_2escm"),(void*)f_2006},
{C_text("f_2009:crypto_2dffi_2escm"),(void*)f_2009},
{C_text("f_2012:crypto_2dffi_2escm"),(void*)f_2012},
{C_text("f_2015:crypto_2dffi_2escm"),(void*)f_2015},
{C_text("f_2021:crypto_2dffi_2escm"),(void*)f_2021},
{C_text("f_2024:crypto_2dffi_2escm"),(void*)f_2024},
{C_text("f_2027:crypto_2dffi_2escm"),(void*)f_2027},
{C_text("f_2030:crypto_2dffi_2escm"),(void*)f_2030},
{C_text("f_2035:crypto_2dffi_2escm"),(void*)f_2035},
{C_text("f_2060:crypto_2dffi_2escm"),(void*)f_2060},
{C_text("f_2068:crypto_2dffi_2escm"),(void*)f_2068},
{C_text("f_2076:crypto_2dffi_2escm"),(void*)f_2076},
{C_text("f_2080:crypto_2dffi_2escm"),(void*)f_2080},
{C_text("f_2086:crypto_2dffi_2escm"),(void*)f_2086},
{C_text("f_2096:crypto_2dffi_2escm"),(void*)f_2096},
{C_text("f_2102:crypto_2dffi_2escm"),(void*)f_2102},
{C_text("f_2105:crypto_2dffi_2escm"),(void*)f_2105},
{C_text("f_2114:crypto_2dffi_2escm"),(void*)f_2114},
{C_text("f_2139:crypto_2dffi_2escm"),(void*)f_2139},
{C_text("f_2143:crypto_2dffi_2escm"),(void*)f_2143},
{C_text("f_2149:crypto_2dffi_2escm"),(void*)f_2149},
{C_text("f_2170:crypto_2dffi_2escm"),(void*)f_2170},
{C_text("f_2176:crypto_2dffi_2escm"),(void*)f_2176},
{C_text("f_2197:crypto_2dffi_2escm"),(void*)f_2197},
{C_text("f_2211:crypto_2dffi_2escm"),(void*)f_2211},
{C_text("f_2214:crypto_2dffi_2escm"),(void*)f_2214},
{C_text("f_2217:crypto_2dffi_2escm"),(void*)f_2217},
{C_text("f_2221:crypto_2dffi_2escm"),(void*)f_2221},
{C_text("f_2224:crypto_2dffi_2escm"),(void*)f_2224},
{C_text("f_2230:crypto_2dffi_2escm"),(void*)f_2230},
{C_text("f_2233:crypto_2dffi_2escm"),(void*)f_2233},
{C_text("f_2236:crypto_2dffi_2escm"),(void*)f_2236},
{C_text("f_2239:crypto_2dffi_2escm"),(void*)f_2239},
{C_text("f_2242:crypto_2dffi_2escm"),(void*)f_2242},
{C_text("f_2247:crypto_2dffi_2escm"),(void*)f_2247},
{C_text("f_2257:crypto_2dffi_2escm"),(void*)f_2257},
{C_text("f_2269:crypto_2dffi_2escm"),(void*)f_2269},
{C_text("f_2279:crypto_2dffi_2escm"),(void*)f_2279},
{C_text("f_2285:crypto_2dffi_2escm"),(void*)f_2285},
{C_text("f_2289:crypto_2dffi_2escm"),(void*)f_2289},
{C_text("f_2300:crypto_2dffi_2escm"),(void*)f_2300},
{C_text("f_2302:crypto_2dffi_2escm"),(void*)f_2302},
{C_text("f_2325:crypto_2dffi_2escm"),(void*)f_2325},
{C_text("f_2329:crypto_2dffi_2escm"),(void*)f_2329},
{C_text("f_2333:crypto_2dffi_2escm"),(void*)f_2333},
{C_text("f_2337:crypto_2dffi_2escm"),(void*)f_2337},
{C_text("f_2349:crypto_2dffi_2escm"),(void*)f_2349},
{C_text("f_2353:crypto_2dffi_2escm"),(void*)f_2353},
{C_text("f_2365:crypto_2dffi_2escm"),(void*)f_2365},
{C_text("f_2379:crypto_2dffi_2escm"),(void*)f_2379},
{C_text("f_2382:crypto_2dffi_2escm"),(void*)f_2382},
{C_text("f_2385:crypto_2dffi_2escm"),(void*)f_2385},
{C_text("f_2388:crypto_2dffi_2escm"),(void*)f_2388},
{C_text("f_2391:crypto_2dffi_2escm"),(void*)f_2391},
{C_text("f_2394:crypto_2dffi_2escm"),(void*)f_2394},
{C_text("f_2397:crypto_2dffi_2escm"),(void*)f_2397},
{C_text("f_867:crypto_2dffi_2escm"),(void*)f_867},
{C_text("f_870:crypto_2dffi_2escm"),(void*)f_870},
{C_text("f_873:crypto_2dffi_2escm"),(void*)f_873},
{C_text("f_876:crypto_2dffi_2escm"),(void*)f_876},
{C_text("f_879:crypto_2dffi_2escm"),(void*)f_879},
{C_text("f_882:crypto_2dffi_2escm"),(void*)f_882},
{C_text("f_889:crypto_2dffi_2escm"),(void*)f_889},
{C_text("f_892:crypto_2dffi_2escm"),(void*)f_892},
{C_text("f_909:crypto_2dffi_2escm"),(void*)f_909},
{C_text("f_913:crypto_2dffi_2escm"),(void*)f_913},
{C_text("f_916:crypto_2dffi_2escm"),(void*)f_916},
{C_text("f_919:crypto_2dffi_2escm"),(void*)f_919},
{C_text("f_924:crypto_2dffi_2escm"),(void*)f_924},
{C_text("f_928:crypto_2dffi_2escm"),(void*)f_928},
{C_text("f_931:crypto_2dffi_2escm"),(void*)f_931},
{C_text("f_934:crypto_2dffi_2escm"),(void*)f_934},
{C_text("f_939:crypto_2dffi_2escm"),(void*)f_939},
{C_text("f_966:crypto_2dffi_2escm"),(void*)f_966},
{C_text("f_970:crypto_2dffi_2escm"),(void*)f_970},
{C_text("f_973:crypto_2dffi_2escm"),(void*)f_973},
{C_text("f_976:crypto_2dffi_2escm"),(void*)f_976},
{C_text("toplevel:crypto_2dffi_2escm"),(void*)C_toplevel},
{NULL,NULL}};
#endif

static C_PTABLE_ENTRY *create_ptable(void){
#ifdef C_ENABLE_PTABLES
return ptable;
#else
return NULL;
#endif
}

/*
o|hiding unexported module binding: crypto-ffi#crypto-hash-sha256-bytes 
o|hiding unexported module binding: crypto-ffi#crypto-hash-sha512-bytes 
o|hiding unexported module binding: crypto-ffi#secretbox-macbytes 
o|hiding unexported module binding: crypto-ffi#argon2id-opslimit-moderate 
o|hiding unexported module binding: crypto-ffi#argon2id-memlimit-moderate 
o|hiding unexported module binding: crypto-ffi#string->u8vector 
o|hiding unexported module binding: crypto-ffi#u8vector->hex 
o|hiding unexported module binding: crypto-ffi#gf256-exp 
o|hiding unexported module binding: crypto-ffi#gf256-log 
o|hiding unexported module binding: crypto-ffi#init-gf256-tables! 
o|hiding unexported module binding: crypto-ffi#gf256-poly-eval 
o|hiding unexported module binding: crypto-ffi#<shamir-share> 
o|hiding unexported module binding: crypto-ffi#make-shamir-share-internal 
S|applied compiler syntax:
S|  chicken.format#sprintf		2
o|eliminated procedure checks: 52 
(o e)|assignments to immediate values: 13 
o|inlining procedure: k899 
o|inlining procedure: k899 
o|inlining procedure: k941 
o|inlining procedure: k941 
o|contracted procedure: "(crypto-ffi.scm:128) g5960" 
o|inlining procedure: k996 
o|inlining procedure: k996 
o|contracted procedure: "(crypto-ffi.scm:151) g8990" 
o|inlining procedure: k1046 
o|inlining procedure: k1046 
o|contracted procedure: "(crypto-ffi.scm:167) g112113" 
o|substituted constant variable: crypto-ffi#crypto-hash-sha256-bytes 
o|contracted procedure: "(crypto-ffi.scm:182) g132133" 
o|substituted constant variable: crypto-ffi#crypto-hash-sha512-bytes 
o|contracted procedure: "(crypto-ffi.scm:205) g153154" 
o|contracted procedure: "(crypto-ffi.scm:253) g189190" 
o|contracted procedure: "(crypto-ffi.scm:263) g203204" 
o|contracted procedure: "(crypto-ffi.scm:273) g217218" 
o|contracted procedure: "(crypto-ffi.scm:280) g223224" 
o|inlining procedure: k1333 
o|inlining procedure: k1333 
o|contracted procedure: "(crypto-ffi.scm:287) g231232" 
o|contracted procedure: "(crypto-ffi.scm:297) g245246" 
o|inlining procedure: k1428 
o|inlining procedure: k1428 
o|contracted procedure: "(crypto-ffi.scm:312) g262263" 
o|substituted constant variable: crypto-ffi#argon2id-opslimit-moderate 
o|substituted constant variable: crypto-ffi#argon2id-memlimit-moderate 
o|inlining procedure: k1494 
o|inlining procedure: k1494 
o|contracted procedure: "(crypto-ffi.scm:340) g299300" 
o|inlining procedure: k1475 
o|inlining procedure: k1475 
o|substituted constant variable: crypto-ffi#secretbox-macbytes 
o|inlining procedure: k1554 
o|inlining procedure: k1554 
o|contracted procedure: "(crypto-ffi.scm:360) g329330" 
o|inlining procedure: k1535 
o|inlining procedure: k1535 
o|substituted constant variable: crypto-ffi#secretbox-macbytes 
o|contracted procedure: "(crypto-ffi.scm:411) g367368" 
o|inlining procedure: k1592 
o|inlining procedure: k1592 
o|inlining procedure: k1639 
o|inlining procedure: k1639 
o|contracted procedure: "(crypto-ffi.scm:425) g385386" 
o|inlining procedure: k1624 
o|inlining procedure: k1624 
o|removed side-effect free assignment to unused variable: crypto-ffi#string->u8vector 
o|removed side-effect free assignment to unused variable: crypto-ffi#u8vector->hex 
o|inlining procedure: k1844 
o|inlining procedure: k1844 
o|inlining procedure: k1878 
o|inlining procedure: k1878 
o|removed side-effect free assignment to unused variable: crypto-ffi#<shamir-share> 
o|inlining procedure: k2037 
o|inlining procedure: k2037 
o|contracted procedure: "(crypto-ffi.scm:583) crypto-ffi#make-shamir-share-internal" 
o|inlining procedure: k2088 
o|inlining procedure: k2088 
o|inlining procedure: k2116 
o|inlining procedure: k2116 
o|contracted procedure: "(crypto-ffi.scm:577) crypto-ffi#gf256-poly-eval" 
o|inlining procedure: k1920 
o|inlining procedure: k1920 
o|inlining procedure: k2151 
o|inlining procedure: k2151 
o|inlining procedure: k2178 
o|inlining procedure: k2178 
o|inlining procedure: k2249 
o|inlining procedure: k2249 
o|inlining procedure: k2271 
o|inlining procedure: k2271 
o|inlining procedure: k2304 
o|inlining procedure: k2304 
o|contracted procedure: "(crypto-ffi.scm:490) crypto-ffi#init-gf256-tables!" 
o|inlining procedure: k1764 
o|inlining procedure: k1764 
o|inlining procedure: k1791 
o|inlining procedure: k1791 
o|replaced variables: 432 
o|removed binding forms: 146 
o|removed side-effect free assignment to unused variable: crypto-ffi#crypto-hash-sha256-bytes 
o|removed side-effect free assignment to unused variable: crypto-ffi#crypto-hash-sha512-bytes 
o|substituted constant variable: r9002410 
o|substituted constant variable: r9002410 
o|substituted constant variable: r9972416 
o|substituted constant variable: r9972416 
o|substituted constant variable: r10472420 
o|substituted constant variable: r10472420 
o|substituted constant variable: unsigned-integer160171 
o|substituted constant variable: scheme-pointer159170 
o|substituted constant variable: scheme-pointer159170 
o|removed side-effect free assignment to unused variable: crypto-ffi#secretbox-macbytes 
o|removed side-effect free assignment to unused variable: crypto-ffi#argon2id-opslimit-moderate 
o|removed side-effect free assignment to unused variable: crypto-ffi#argon2id-memlimit-moderate 
o|substituted constant variable: unsigned-integer206211 
o|substituted constant variable: r13342422 
o|substituted constant variable: r13342422 
o|inlining procedure: k1333 
o|inlining procedure: k1333 
o|substituted constant variable: int271284 
o|substituted constant variable: unsigned-integer270283 
o|substituted constant variable: unsigned-integer269282 
o|substituted constant variable: r14762432 
o|substituted constant variable: r14762432 
o|substituted constant variable: r15552435 
o|substituted constant variable: r15362438 
o|substituted constant variable: r15362438 
o|substituted constant variable: r15932442 
o|substituted constant variable: r15932442 
o|substituted constant variable: r16252448 
o|substituted constant variable: r16252448 
o|substituted constant variable: r18452450 
o|substituted constant variable: r18792452 
o|replaced variables: 113 
o|removed binding forms: 321 
o|removed conditional forms: 1 
o|inlining procedure: k1012 
o|inlining procedure: k1012 
o|inlining procedure: k1059 
o|inlining procedure: k1059 
o|inlining procedure: k1105 
o|inlining procedure: k1148 
o|contracted procedure: k1190 
o|inlining procedure: k1209 
o|inlining procedure: k1249 
o|inlining procedure: k1601 
o|inlining procedure: k1601 
o|inlining procedure: k2310 
o|inlining procedure: k2310 
o|inlining procedure: k1803 
o|inlining procedure: k1803 
o|removed binding forms: 108 
o|substituted constant variable: r1191 
o|contracted procedure: k1272 
o|substituted constant variable: r13342482 
o|substituted constant variable: r13342484 
o|contracted procedure: k1425 
o|removed binding forms: 15 
o|removed binding forms: 3 
o|simplifications: ((let . 3) (if . 31) (##core#call . 171)) 
o|  call simplifications:
o|    chicken.bitwise#arithmetic-shift
o|    scheme#null?
o|    scheme#>=	2
o|    scheme#car	2
o|    scheme#not
o|    scheme#<=
o|    srfi-4#u8vector-length
o|    scheme#>	2
o|    scheme#length	2
o|    scheme#<	2
o|    scheme#list-ref	4
o|    scheme#vector-ref	2
o|    ##sys#make-structure
o|    scheme#vector-set!	4
o|    ##sys#check-structure	4
o|    ##sys#block-ref	4
o|    ##sys#structure?
o|    scheme#modulo	2
o|    chicken.bitwise#bitwise-xor	3
o|    scheme#-	6
o|    scheme#string=?	2
o|    ##sys#cons	5
o|    ##sys#list
o|    ##sys#foreign-fixnum-argument	2
o|    scheme#string?	6
o|    ##sys#foreign-unsigned-ranged-integer-argument	16
o|    scheme#=	20
o|    srfi-4#u8vector-ref	11
o|    srfi-4#u8vector-set!	6
o|    scheme#+	19
o|    scheme#list	3
o|    ##sys#foreign-block-argument	34
o|contracted procedure: k895 
o|contracted procedure: k899 
o|contracted procedure: k944 
o|contracted procedure: k962 
o|contracted procedure: k958 
o|contracted procedure: k947 
o|contracted procedure: k954 
o|contracted procedure: k980 
o|contracted procedure: k984 
o|contracted procedure: k988 
o|contracted procedure: k992 
o|contracted procedure: k996 
o|contracted procedure: k1019 
o|contracted procedure: k1034 
o|contracted procedure: k1038 
o|contracted procedure: k1042 
o|contracted procedure: k1046 
o|contracted procedure: k1069 
o|contracted procedure: k1087 
o|contracted procedure: k1091 
o|contracted procedure: k1095 
o|contracted procedure: k1112 
o|contracted procedure: k1130 
o|contracted procedure: k1134 
o|contracted procedure: k1138 
o|contracted procedure: k1155 
o|contracted procedure: k1174 
o|contracted procedure: k1178 
o|propagated global variable: unsigned-integer156167 crypto-ffi#crypto-generichash-bytes 
o|contracted procedure: k1182 
o|contracted procedure: k1186 
o|contracted procedure: k1194 
o|contracted procedure: k1216 
o|contracted procedure: k1238 
o|contracted procedure: k1242 
o|contracted procedure: k1261 
o|contracted procedure: k1265 
o|contracted procedure: k1299 
o|contracted procedure: k1321 
o|contracted procedure: k1329 
o|contracted procedure: k1336 
o|contracted procedure: k1342 
o|contracted procedure: k1351 
o|contracted procedure: k1355 
o|contracted procedure: k1381 
o|contracted procedure: k1385 
o|propagated global variable: unsigned-integer265278 crypto-ffi#secretbox-keybytes 
o|contracted procedure: k1389 
o|contracted procedure: k1393 
o|contracted procedure: k1397 
o|contracted procedure: k1401 
o|contracted procedure: k1405 
o|contracted procedure: k1409 
o|contracted procedure: k1431 
o|contracted procedure: k1441 
o|contracted procedure: k1497 
o|contracted procedure: k1459 
o|contracted procedure: k1463 
o|contracted procedure: k1467 
o|contracted procedure: k1471 
o|contracted procedure: k1475 
o|contracted procedure: k1504 
o|contracted procedure: k1557 
o|contracted procedure: k1519 
o|contracted procedure: k1523 
o|contracted procedure: k1527 
o|contracted procedure: k1531 
o|contracted procedure: k1535 
o|contracted procedure: k1561 
o|contracted procedure: k1588 
o|contracted procedure: k1592 
o|contracted procedure: k1642 
o|contracted procedure: k1616 
o|contracted procedure: k1620 
o|contracted procedure: k1624 
o|contracted procedure: k1847 
o|contracted procedure: k1850 
o|contracted procedure: k1865 
o|contracted procedure: k1869 
o|contracted procedure: k1861 
o|contracted procedure: k1857 
o|contracted procedure: k1881 
o|contracted procedure: k1904 
o|contracted procedure: k1896 
o|contracted procedure: k1900 
o|contracted procedure: k1892 
o|contracted procedure: k1888 
o|contracted procedure: k1965 
o|contracted procedure: k1974 
o|contracted procedure: k1983 
o|contracted procedure: k1992 
o|contracted procedure: k2016 
o|contracted procedure: k2040 
o|contracted procedure: k2062 
o|contracted procedure: k2054 
o|contracted procedure: k2043 
o|contracted procedure: k2050 
o|contracted procedure: k2070 
o|contracted procedure: k2082 
o|contracted procedure: k2091 
o|contracted procedure: k2172 
o|contracted procedure: k2097 
o|contracted procedure: k2110 
o|contracted procedure: k2119 
o|contracted procedure: k2145 
o|contracted procedure: k2133 
o|contracted procedure: k2122 
o|contracted procedure: k2129 
o|contracted procedure: k1946 
o|contracted procedure: k1914 
o|contracted procedure: k1923 
o|contracted procedure: k1930 
o|contracted procedure: k1938 
o|contracted procedure: k2154 
o|contracted procedure: k2157 
o|contracted procedure: k2164 
o|contracted procedure: k2181 
o|contracted procedure: k2184 
o|contracted procedure: k2191 
o|contracted procedure: k2198 
o|contracted procedure: k2204 
o|contracted procedure: k2225 
o|contracted procedure: k2252 
o|contracted procedure: k2258 
o|contracted procedure: k2265 
o|contracted procedure: k2274 
o|contracted procedure: k2280 
o|contracted procedure: k2294 
o|contracted procedure: k2307 
o|contracted procedure: k2343 
o|contracted procedure: k2320 
o|contracted procedure: k23172539 
o|contracted procedure: k2339 
o|contracted procedure: k23172543 
o|contracted procedure: k2355 
o|contracted procedure: k2359 
o|contracted procedure: k2367 
o|contracted procedure: k2370 
o|contracted procedure: k2399 
o|contracted procedure: k2402 
o|contracted procedure: k1767 
o|contracted procedure: k1785 
o|contracted procedure: k1781 
o|contracted procedure: k1770 
o|contracted procedure: k1777 
o|contracted procedure: k1794 
o|contracted procedure: k1797 
o|contracted procedure: k1800 
o|contracted procedure: k1813 
o|contracted procedure: k1816 
o|contracted procedure: k1826 
o|contracted procedure: k1819 
o|contracted procedure: k1823 
o|contracted procedure: k18102555 
o|contracted procedure: k18102559 
o|simplifications: ((if . 4) (let . 41)) 
o|removed binding forms: 153 
o|inlining procedure: k1325 
o|inlining procedure: k1325 
o|contracted procedure: k1491 
o|contracted procedure: k1551 
o|contracted procedure: k1636 
o|removed binding forms: 3 
o|removed binding forms: 1 
o|customizable procedures: (doloop432433 doloop430441 doloop569570 doloop563564 doloop559560 doloop506509 doloop516518 loop461 doloop517522 doloop507513 doloop508530 doloop4849) 
o|calls to known targets: 36 
o|identified direct recursive calls: f_939 1 
o|identified direct recursive calls: f_2302 1 
o|identified direct recursive calls: f_1762 1 
o|identified direct recursive calls: f_1789 2 
o|fast box initializations: 12 
o|fast global references: 10 
o|fast global assignments: 2 
*/
/* end of file */
