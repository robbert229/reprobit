	TITLE	homed.c
	.386P
include listing.inc
if @Version gt 510
.model FLAT
else
_TEXT	SEGMENT PARA USE32 PUBLIC 'CODE'
_TEXT	ENDS
_DATA	SEGMENT DWORD USE32 PUBLIC 'DATA'
_DATA	ENDS
CONST	SEGMENT DWORD USE32 PUBLIC 'CONST'
CONST	ENDS
_BSS	SEGMENT DWORD USE32 PUBLIC 'BSS'
_BSS	ENDS
$$SYMBOLS	SEGMENT BYTE USE32 'DEBSYM'
$$SYMBOLS	ENDS
$$TYPES	SEGMENT BYTE USE32 'DEBTYP'
$$TYPES	ENDS
_TLS	SEGMENT DWORD USE32 PUBLIC 'TLS'
_TLS	ENDS
;	COMDAT _homed_draw
_TEXT	SEGMENT PARA USE32 PUBLIC 'CODE'
_TEXT	ENDS
FLAT	GROUP _DATA, CONST, _BSS
	ASSUME	CS: FLAT, DS: FLAT, SS: FLAT
endif
PUBLIC	_homed_draw
EXTRN	_icon_draw:NEAR
EXTRN	__fltused:NEAR
;	COMDAT _homed_draw
_TEXT	SEGMENT
_row$ = 8
_across$ = 12
_down$ = 16
_pos$ = -24
_i$ = 16
_homed_draw PROC NEAR					; COMDAT

; 11   : {

	sub	esp, 24					; 00000018H

; 12   :     Point pos;
; 13   :     unsigned int x;
; 14   :     unsigned int height;
; 15   :     unsigned int i;
; 16   : 
; 17   :     x = 0;
; 18   :     height = 0;
; 19   :     pos.y = (float)down;

	mov	eax, DWORD PTR _down$[esp+20]

; 20   :     across += down;
; 21   :     for (i = 0; i < row->count; i++) {

	mov	edx, DWORD PTR _row$[esp+20]
	push	ebx
	push	ebp
	mov	ebp, DWORD PTR _across$[esp+28]
	xor	ecx, ecx
	mov	DWORD PTR -24+[esp+32], eax
	mov	DWORD PTR -24+[esp+36], ecx
	fild	QWORD PTR -24+[esp+32]
	add	ebp, eax
	mov	eax, DWORD PTR [edx+32]
	push	esi
	xor	ebx, ebx
	fstp	DWORD PTR _pos$[esp+40]
	xor	esi, esi
	cmp	eax, ecx
	mov	DWORD PTR _i$[esp+32], ecx
	jbe	SHORT $L101
	push	edi
	mov	edi, edx
$L99:

; 22   :         if (row->icons[i]) {

	mov	eax, DWORD PTR [edi]
	cmp	eax, ecx
	je	SHORT $L102

; 23   :             pos.x = (float)(x + across);

	lea	edx, DWORD PTR [ebx+ebp]
	mov	DWORD PTR -16+[esp+44], ecx
	mov	DWORD PTR -16+[esp+40], edx

; 24   :             icon_draw(row->icons[i], &pos);

	lea	ecx, DWORD PTR _pos$[esp+40]
	fild	QWORD PTR -16+[esp+40]
	push	ecx
	push	eax
	fstp	DWORD PTR _pos$[esp+48]
	call	_icon_draw

; 25   :             if ((int)row->icons[i]->height > (int)height) height = row->icons[i]->height;

	mov	ecx, DWORD PTR [edi]
	add	esp, 8
	mov	eax, DWORD PTR [ecx+4]
	cmp	eax, esi
	jle	SHORT $L103
	mov	esi, eax
$L103:

; 26   :             x += row->icons[i]->width;

	mov	eax, DWORD PTR [ecx]

; 27   :         }
; 28   :         else {

	mov	edx, DWORD PTR _row$[esp+36]
	add	ebx, eax
	xor	ecx, ecx
	jmp	SHORT $L100
$L102:

; 29   :             pos.y += height;

	mov	DWORD PTR -8+[esp+40], esi
	mov	DWORD PTR -8+[esp+44], ecx
	fild	QWORD PTR -8+[esp+40]

; 30   :             height = 0;

	xor	esi, esi

; 31   :             x = 0;

	xor	ebx, ebx
	fadd	DWORD PTR _pos$[esp+44]
	fstp	DWORD PTR _pos$[esp+44]
$L100:
	mov	eax, DWORD PTR _i$[esp+36]
	add	edi, 4
	inc	eax
	cmp	eax, DWORD PTR [edx+32]
	mov	DWORD PTR _i$[esp+36], eax
	jb	SHORT $L99

; 11   : {

	pop	edi
$L101:

; 32   :         }
; 33   :     }
; 34   : }

	pop	esi
	pop	ebp
	pop	ebx
	add	esp, 24					; 00000018H
	ret	0
_homed_draw ENDP
_TEXT	ENDS
END
