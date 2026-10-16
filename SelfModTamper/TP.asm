option casemap :none

.code

; _TEXT$SMC SEGMENT ALIGN(4096)

; http://ref.x86asm.net/coder.html
; 3 bits - 000/001/010/011/100/101/110/111
; ADD/OR/ADC/SBB/AND/SUB/XOR/CMP 
; ROL/ROR/RCL/RCR/SHL/SHR/SAL/SAR
; FADD/FMUL/FCOM/FCOMP/FSUB/FSUBR/FDIV/FDIVR
; 1 bit - 0/1 INC/DEC CLC/STC CLI/STI CLD/STD
; conditions in JC, SETC, CMOV instructions O/NO/B,NAE,C/NB,AE,NC/Z,E/NZ,NE/BE,NA/NBE,A/S,NS/P,PE/NP,PO/L,NGE/NL,GE/LE,NG/NLE,G
; JC rel8 70-7F vs JC rel16/32 0F 80 - 0F 8F
; JMP rel8 EB vs JMP E9 rel16/32
;x64 calling convention passes arguments fastcall: RCX, RDX, R8, R9, on stack but using default argument scheme uses stack and without first 4 indexes them incorrectly
TPComp PROC USES rbx rsi rdi
MOV RSI, RCX
LEA RDI, [RSI+RDX]
XOR RBX, RBX
; PUSH RCX ; CPU signature initialized by privileged software
; RDTSC
; RDTSCP ; requires CR4.TSD (control register 4, time stamp disable) not to be set otherwise requires ring 0 access
; SHL RDX, 32
; OR RAX, RDX
; PUSH RAX
CLC
checksum:
ADC RBX, QWORD PTR [RSI] ; 48 13 1E
SETS DL ; 0F 98 C2
SETP AL ; 0F 9A C0
SHL AL, 2 ; C0 E0 02
OR DL, AL ; 0A D0
SHL DL, 3 ; C0 E2 03
XOR BYTE PTR [$-2-3-3-3-2-3], DL
LEA RSI, [RSI+8]
CMP RDI, RSI
JG checksum

MOV QWORD PTR [R8], RBX

; RDTSCP
; SHL RDX, 32
; OR RAX, RDX
; POP RBX
; SUB RAX, RBX
RET
TPComp ENDP

; _TEXT$SMC ENDS
; Note: the segment above (commented out) would have enclosed TPComp only. TPCompLoop below is in the ordinary .text section, so
; the static unrolled loop is not page-aligned (the dynamic copy made by gen_asm is, via VirtualAlloc). Precondition of TPCompLoop:
; the byte count in RDX is at least 8 and a multiple of 8.

TPCompLoop PROC USES rbx rsi rdi
mov rdi, rdx
xor rbx, rbx
L0:
sub rdi, 2368
jg L1
add rdi, 2368
shr rdi, 3
dec rdi
imul rsi, rdi, 27
cmp rdi, 148
jl L2
add esi, 5
L2:
mov rax, 7974
sub rax, rsi
shl rax, 8
mov rdi, 309376683425
xor rdi, rax
add dword ptr [L4-4], esi
xor qword ptr [L3+23], rdi
L4:
sub dword ptr [L4-4], esi
L1:
clc
L3:
L5:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L153+1], dl
lea rcx, [rcx+8]
L6:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L154+1], dl
lea rcx, [rcx+8]
L7:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L155+1], dl
lea rcx, [rcx+8]
L8:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L156+1], dl
lea rcx, [rcx+8]
L9:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L157+1], dl
lea rcx, [rcx+8]
L10:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L158+1], dl
lea rcx, [rcx+8]
L11:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L159+1], dl
lea rcx, [rcx+8]
L12:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L160+1], dl
lea rcx, [rcx+8]
L13:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L161+1], dl
lea rcx, [rcx+8]
L14:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L162+1], dl
lea rcx, [rcx+8]
L15:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L163+1], dl
lea rcx, [rcx+8]
L16:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L164+1], dl
lea rcx, [rcx+8]
L17:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L165+1], dl
lea rcx, [rcx+8]
L18:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L166+1], dl
lea rcx, [rcx+8]
L19:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L167+1], dl
lea rcx, [rcx+8]
L20:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L168+1], dl
lea rcx, [rcx+8]
L21:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L169+1], dl
lea rcx, [rcx+8]
L22:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L170+1], dl
lea rcx, [rcx+8]
L23:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L171+1], dl
lea rcx, [rcx+8]
L24:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L172+1], dl
lea rcx, [rcx+8]
L25:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L173+1], dl
lea rcx, [rcx+8]
L26:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L174+1], dl
lea rcx, [rcx+8]
L27:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L175+1], dl
lea rcx, [rcx+8]
L28:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L176+1], dl
lea rcx, [rcx+8]
L29:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L177+1], dl
lea rcx, [rcx+8]
L30:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L178+1], dl
lea rcx, [rcx+8]
L31:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L179+1], dl
lea rcx, [rcx+8]
L32:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L180+1], dl
lea rcx, [rcx+8]
L33:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L181+1], dl
lea rcx, [rcx+8]
L34:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L182+1], dl
lea rcx, [rcx+8]
L35:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L183+1], dl
lea rcx, [rcx+8]
L36:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L184+1], dl
lea rcx, [rcx+8]
L37:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L185+1], dl
lea rcx, [rcx+8]
L38:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L186+1], dl
lea rcx, [rcx+8]
L39:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L187+1], dl
lea rcx, [rcx+8]
L40:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L188+1], dl
lea rcx, [rcx+8]
L41:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L189+1], dl
lea rcx, [rcx+8]
L42:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L190+1], dl
lea rcx, [rcx+8]
L43:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L191+1], dl
lea rcx, [rcx+8]
L44:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L192+1], dl
lea rcx, [rcx+8]
L45:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L193+1], dl
lea rcx, [rcx+8]
L46:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L194+1], dl
lea rcx, [rcx+8]
L47:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L195+1], dl
lea rcx, [rcx+8]
L48:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L196+1], dl
lea rcx, [rcx+8]
L49:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L197+1], dl
lea rcx, [rcx+8]
L50:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L198+1], dl
lea rcx, [rcx+8]
L51:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L199+1], dl
lea rcx, [rcx+8]
L52:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L200+1], dl
lea rcx, [rcx+8]
L53:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L201+1], dl
lea rcx, [rcx+8]
L54:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L202+1], dl
lea rcx, [rcx+8]
L55:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L203+1], dl
lea rcx, [rcx+8]
L56:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L204+1], dl
lea rcx, [rcx+8]
L57:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L205+1], dl
lea rcx, [rcx+8]
L58:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L206+1], dl
lea rcx, [rcx+8]
L59:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L207+1], dl
lea rcx, [rcx+8]
L60:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L208+1], dl
lea rcx, [rcx+8]
L61:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L209+1], dl
lea rcx, [rcx+8]
L62:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L210+1], dl
lea rcx, [rcx+8]
L63:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L211+1], dl
lea rcx, [rcx+8]
L64:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L212+1], dl
lea rcx, [rcx+8]
L65:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L213+1], dl
lea rcx, [rcx+8]
L66:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L214+1], dl
lea rcx, [rcx+8]
L67:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L215+1], dl
lea rcx, [rcx+8]
L68:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L216+1], dl
lea rcx, [rcx+8]
L69:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L217+1], dl
lea rcx, [rcx+8]
L70:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L218+1], dl
lea rcx, [rcx+8]
L71:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L219+1], dl
lea rcx, [rcx+8]
L72:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L220+1], dl
lea rcx, [rcx+8]
L73:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L221+1], dl
lea rcx, [rcx+8]
L74:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L222+1], dl
lea rcx, [rcx+8]
L75:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L223+1], dl
lea rcx, [rcx+8]
L76:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L224+1], dl
lea rcx, [rcx+8]
L77:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L225+1], dl
lea rcx, [rcx+8]
L78:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L226+1], dl
lea rcx, [rcx+8]
L79:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L227+1], dl
lea rcx, [rcx+8]
L80:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L228+1], dl
lea rcx, [rcx+8]
L81:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L229+1], dl
lea rcx, [rcx+8]
L82:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L230+1], dl
lea rcx, [rcx+8]
L83:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L231+1], dl
lea rcx, [rcx+8]
L84:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L232+1], dl
lea rcx, [rcx+8]
L85:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L233+1], dl
lea rcx, [rcx+8]
L86:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L234+1], dl
lea rcx, [rcx+8]
L87:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L235+1], dl
lea rcx, [rcx+8]
L88:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L236+1], dl
lea rcx, [rcx+8]
L89:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L237+1], dl
lea rcx, [rcx+8]
L90:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L238+1], dl
lea rcx, [rcx+8]
L91:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L239+1], dl
lea rcx, [rcx+8]
L92:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L240+1], dl
lea rcx, [rcx+8]
L93:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L241+1], dl
lea rcx, [rcx+8]
L94:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L242+1], dl
lea rcx, [rcx+8]
L95:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L243+1], dl
lea rcx, [rcx+8]
L96:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L244+1], dl
lea rcx, [rcx+8]
L97:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L245+1], dl
lea rcx, [rcx+8]
L98:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L246+1], dl
lea rcx, [rcx+8]
L99:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L247+1], dl
lea rcx, [rcx+8]
L100:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L248+1], dl
lea rcx, [rcx+8]
L101:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L249+1], dl
lea rcx, [rcx+8]
L102:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L250+1], dl
lea rcx, [rcx+8]
L103:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L251+1], dl
lea rcx, [rcx+8]
L104:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L252+1], dl
lea rcx, [rcx+8]
L105:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L253+1], dl
lea rcx, [rcx+8]
L106:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L254+1], dl
lea rcx, [rcx+8]
L107:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L255+1], dl
lea rcx, [rcx+8]
L108:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L256+1], dl
lea rcx, [rcx+8]
L109:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L257+1], dl
lea rcx, [rcx+8]
L110:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L258+1], dl
lea rcx, [rcx+8]
L111:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L259+1], dl
lea rcx, [rcx+8]
L112:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L260+1], dl
lea rcx, [rcx+8]
L113:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L261+1], dl
lea rcx, [rcx+8]
L114:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L262+1], dl
lea rcx, [rcx+8]
L115:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L263+1], dl
lea rcx, [rcx+8]
L116:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L264+1], dl
lea rcx, [rcx+8]
L117:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L265+1], dl
lea rcx, [rcx+8]
L118:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L266+1], dl
lea rcx, [rcx+8]
L119:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L267+1], dl
lea rcx, [rcx+8]
L120:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L268+1], dl
lea rcx, [rcx+8]
L121:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L269+1], dl
lea rcx, [rcx+8]
L122:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L270+1], dl
lea rcx, [rcx+8]
L123:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L271+1], dl
lea rcx, [rcx+8]
L124:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L272+1], dl
lea rcx, [rcx+8]
L125:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L273+1], dl
lea rcx, [rcx+8]
L126:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L274+1], dl
lea rcx, [rcx+8]
L127:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L275+1], dl
lea rcx, [rcx+8]
L128:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L276+1], dl
lea rcx, [rcx+8]
L129:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L277+1], dl
lea rcx, [rcx+8]
L130:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L278+1], dl
lea rcx, [rcx+8]
L131:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L279+1], dl
lea rcx, [rcx+8]
L132:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L280+1], dl
lea rcx, [rcx+8]
L133:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L281+1], dl
lea rcx, [rcx+8]
L134:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L282+1], dl
lea rcx, [rcx+8]
L135:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L283+1], dl
lea rcx, [rcx+8]
L136:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L284+1], dl
lea rcx, [rcx+8]
L137:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L285+1], dl
lea rcx, [rcx+8]
L138:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L286+1], dl
lea rcx, [rcx+8]
L139:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L287+1], dl
lea rcx, [rcx+8]
L140:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L288+1], dl
lea rcx, [rcx+8]
L141:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L289+1], dl
lea rcx, [rcx+8]
L142:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L290+1], dl
lea rcx, [rcx+8]
L143:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L291+1], dl
lea rcx, [rcx+8]
L144:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L292+1], dl
lea rcx, [rcx+8]
L145:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L293+1], dl
lea rcx, [rcx+8]
L146:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L294+1], dl
lea rcx, [rcx+8]
L147:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L295+1], dl
lea rcx, [rcx+8]
L148:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L296+1], dl
lea rcx, [rcx+8]
L149:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L297+1], dl
lea rcx, [rcx+8]
L150:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L298+1], dl
lea rcx, [rcx+8]
L151:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L299+1], dl
lea rcx, [rcx+8]
L152:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L300+1], dl
lea rcx, [rcx+8]
nop
nop
nop
nop
nop
L153:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L5+1], dl
lea rcx, [rcx+8]
L154:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L6+1], dl
lea rcx, [rcx+8]
L155:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L7+1], dl
lea rcx, [rcx+8]
L156:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L8+1], dl
lea rcx, [rcx+8]
L157:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L9+1], dl
lea rcx, [rcx+8]
L158:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L10+1], dl
lea rcx, [rcx+8]
L159:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L11+1], dl
lea rcx, [rcx+8]
L160:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L12+1], dl
lea rcx, [rcx+8]
L161:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L13+1], dl
lea rcx, [rcx+8]
L162:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L14+1], dl
lea rcx, [rcx+8]
L163:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L15+1], dl
lea rcx, [rcx+8]
L164:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L16+1], dl
lea rcx, [rcx+8]
L165:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L17+1], dl
lea rcx, [rcx+8]
L166:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L18+1], dl
lea rcx, [rcx+8]
L167:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L19+1], dl
lea rcx, [rcx+8]
L168:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L20+1], dl
lea rcx, [rcx+8]
L169:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L21+1], dl
lea rcx, [rcx+8]
L170:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L22+1], dl
lea rcx, [rcx+8]
L171:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L23+1], dl
lea rcx, [rcx+8]
L172:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L24+1], dl
lea rcx, [rcx+8]
L173:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L25+1], dl
lea rcx, [rcx+8]
L174:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L26+1], dl
lea rcx, [rcx+8]
L175:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L27+1], dl
lea rcx, [rcx+8]
L176:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L28+1], dl
lea rcx, [rcx+8]
L177:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L29+1], dl
lea rcx, [rcx+8]
L178:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L30+1], dl
lea rcx, [rcx+8]
L179:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L31+1], dl
lea rcx, [rcx+8]
L180:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L32+1], dl
lea rcx, [rcx+8]
L181:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L33+1], dl
lea rcx, [rcx+8]
L182:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L34+1], dl
lea rcx, [rcx+8]
L183:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L35+1], dl
lea rcx, [rcx+8]
L184:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L36+1], dl
lea rcx, [rcx+8]
L185:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L37+1], dl
lea rcx, [rcx+8]
L186:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L38+1], dl
lea rcx, [rcx+8]
L187:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L39+1], dl
lea rcx, [rcx+8]
L188:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L40+1], dl
lea rcx, [rcx+8]
L189:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L41+1], dl
lea rcx, [rcx+8]
L190:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L42+1], dl
lea rcx, [rcx+8]
L191:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L43+1], dl
lea rcx, [rcx+8]
L192:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L44+1], dl
lea rcx, [rcx+8]
L193:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L45+1], dl
lea rcx, [rcx+8]
L194:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L46+1], dl
lea rcx, [rcx+8]
L195:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L47+1], dl
lea rcx, [rcx+8]
L196:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L48+1], dl
lea rcx, [rcx+8]
L197:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L49+1], dl
lea rcx, [rcx+8]
L198:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L50+1], dl
lea rcx, [rcx+8]
L199:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L51+1], dl
lea rcx, [rcx+8]
L200:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L52+1], dl
lea rcx, [rcx+8]
L201:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L53+1], dl
lea rcx, [rcx+8]
L202:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L54+1], dl
lea rcx, [rcx+8]
L203:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L55+1], dl
lea rcx, [rcx+8]
L204:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L56+1], dl
lea rcx, [rcx+8]
L205:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L57+1], dl
lea rcx, [rcx+8]
L206:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L58+1], dl
lea rcx, [rcx+8]
L207:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L59+1], dl
lea rcx, [rcx+8]
L208:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L60+1], dl
lea rcx, [rcx+8]
L209:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L61+1], dl
lea rcx, [rcx+8]
L210:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L62+1], dl
lea rcx, [rcx+8]
L211:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L63+1], dl
lea rcx, [rcx+8]
L212:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L64+1], dl
lea rcx, [rcx+8]
L213:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L65+1], dl
lea rcx, [rcx+8]
L214:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L66+1], dl
lea rcx, [rcx+8]
L215:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L67+1], dl
lea rcx, [rcx+8]
L216:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L68+1], dl
lea rcx, [rcx+8]
L217:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L69+1], dl
lea rcx, [rcx+8]
L218:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L70+1], dl
lea rcx, [rcx+8]
L219:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L71+1], dl
lea rcx, [rcx+8]
L220:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L72+1], dl
lea rcx, [rcx+8]
L221:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L73+1], dl
lea rcx, [rcx+8]
L222:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L74+1], dl
lea rcx, [rcx+8]
L223:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L75+1], dl
lea rcx, [rcx+8]
L224:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L76+1], dl
lea rcx, [rcx+8]
L225:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L77+1], dl
lea rcx, [rcx+8]
L226:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L78+1], dl
lea rcx, [rcx+8]
L227:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L79+1], dl
lea rcx, [rcx+8]
L228:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L80+1], dl
lea rcx, [rcx+8]
L229:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L81+1], dl
lea rcx, [rcx+8]
L230:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L82+1], dl
lea rcx, [rcx+8]
L231:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L83+1], dl
lea rcx, [rcx+8]
L232:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L84+1], dl
lea rcx, [rcx+8]
L233:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L85+1], dl
lea rcx, [rcx+8]
L234:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L86+1], dl
lea rcx, [rcx+8]
L235:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L87+1], dl
lea rcx, [rcx+8]
L236:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L88+1], dl
lea rcx, [rcx+8]
L237:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L89+1], dl
lea rcx, [rcx+8]
L238:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L90+1], dl
lea rcx, [rcx+8]
L239:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L91+1], dl
lea rcx, [rcx+8]
L240:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L92+1], dl
lea rcx, [rcx+8]
L241:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L93+1], dl
lea rcx, [rcx+8]
L242:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L94+1], dl
lea rcx, [rcx+8]
L243:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L95+1], dl
lea rcx, [rcx+8]
L244:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L96+1], dl
lea rcx, [rcx+8]
L245:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L97+1], dl
lea rcx, [rcx+8]
L246:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L98+1], dl
lea rcx, [rcx+8]
L247:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L99+1], dl
lea rcx, [rcx+8]
L248:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L100+1], dl
lea rcx, [rcx+8]
L249:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L101+1], dl
lea rcx, [rcx+8]
L250:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L102+1], dl
lea rcx, [rcx+8]
L251:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L103+1], dl
lea rcx, [rcx+8]
L252:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L104+1], dl
lea rcx, [rcx+8]
L253:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L105+1], dl
lea rcx, [rcx+8]
L254:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L106+1], dl
lea rcx, [rcx+8]
L255:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L107+1], dl
lea rcx, [rcx+8]
L256:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L108+1], dl
lea rcx, [rcx+8]
L257:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L109+1], dl
lea rcx, [rcx+8]
L258:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L110+1], dl
lea rcx, [rcx+8]
L259:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L111+1], dl
lea rcx, [rcx+8]
L260:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L112+1], dl
lea rcx, [rcx+8]
L261:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L113+1], dl
lea rcx, [rcx+8]
L262:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L114+1], dl
lea rcx, [rcx+8]
L263:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L115+1], dl
lea rcx, [rcx+8]
L264:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L116+1], dl
lea rcx, [rcx+8]
L265:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L117+1], dl
lea rcx, [rcx+8]
L266:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L118+1], dl
lea rcx, [rcx+8]
L267:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L119+1], dl
lea rcx, [rcx+8]
L268:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L120+1], dl
lea rcx, [rcx+8]
L269:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L121+1], dl
lea rcx, [rcx+8]
L270:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L122+1], dl
lea rcx, [rcx+8]
L271:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L123+1], dl
lea rcx, [rcx+8]
L272:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L124+1], dl
lea rcx, [rcx+8]
L273:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L125+1], dl
lea rcx, [rcx+8]
L274:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L126+1], dl
lea rcx, [rcx+8]
L275:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L127+1], dl
lea rcx, [rcx+8]
L276:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L128+1], dl
lea rcx, [rcx+8]
L277:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L129+1], dl
lea rcx, [rcx+8]
L278:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L130+1], dl
lea rcx, [rcx+8]
L279:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L131+1], dl
lea rcx, [rcx+8]
L280:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L132+1], dl
lea rcx, [rcx+8]
L281:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L133+1], dl
lea rcx, [rcx+8]
L282:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L134+1], dl
lea rcx, [rcx+8]
L283:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L135+1], dl
lea rcx, [rcx+8]
L284:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L136+1], dl
lea rcx, [rcx+8]
L285:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L137+1], dl
lea rcx, [rcx+8]
L286:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L138+1], dl
lea rcx, [rcx+8]
L287:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L139+1], dl
lea rcx, [rcx+8]
L288:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L140+1], dl
lea rcx, [rcx+8]
L289:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L141+1], dl
lea rcx, [rcx+8]
L290:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L142+1], dl
lea rcx, [rcx+8]
L291:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L143+1], dl
lea rcx, [rcx+8]
L292:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L144+1], dl
lea rcx, [rcx+8]
L293:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L145+1], dl
lea rcx, [rcx+8]
L294:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L146+1], dl
lea rcx, [rcx+8]
L295:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L147+1], dl
lea rcx, [rcx+8]
L296:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L148+1], dl
lea rcx, [rcx+8]
L297:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L149+1], dl
lea rcx, [rcx+8]
L298:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L150+1], dl
lea rcx, [rcx+8]
L299:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L151+1], dl
lea rcx, [rcx+8]
L300:
adc rbx, [rcx]
sets dl
setp al
shl al, 2
or dl, al
shl dl, 3
xor byte ptr [L152+1], dl
lea rcx, [rcx+8]
jmp L0
add dword ptr [L301-4], esi
xor qword ptr [L5+23], rdi
L301:
sub dword ptr [L301-4], esi
mov qword ptr [r8], rbx
ret
TPCompLoop ENDP

END