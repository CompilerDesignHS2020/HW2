open Assert
open Simulator
open X86
open Asm

(* Test suite for asm.ml *)

(* Do NOT modify this file -- we will overwrite it with our *)
(* own version when we test your project.                   *)

(* These tests will be used to grade your assignment *)

(* Example Programs *)

let helloworld = [ text "foo"
                            [ Xorq, [~%Rax; ~%Rax]
                            ; Movq, [~$100; ~%Rax]
                            ; Retq, []
                            ]
                     ; text "main" 
                            [ Xorq, [~%Rax; ~%Rax]
                            ; Movq, [Ind1 (Lbl "baz"); ~%Rax]
                            ; Retq, []
                            ]
                     ; data "baz" 
                            [ Quad (Lit 99L)
                            ; Asciz "Hello, world!"
                            ]
                     ]


let helloworld_textseg =
  [ InsB0 (Xorq, [Reg Rax; Reg Rax]);              InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ; InsB0 (Movq, [Imm (Lit 100L); Reg Rax]);       InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ; InsB0 (Retq, []);                              InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ; InsB0 (Xorq, [Reg Rax; Reg Rax]);              InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ; InsB0 (Movq, [Ind1 (Lit 0x400030L); Reg Rax]); InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ; InsB0 (Retq, []);                              InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ]

let provided_tests : suite = [
  Test ("Debug", [ 
    ("assemble1", assert_eqf (fun () -> (assemble helloworld).text_seg) helloworld_textseg )
    ]);

] 



