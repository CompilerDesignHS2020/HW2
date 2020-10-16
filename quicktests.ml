(* 

(Simulator.assemble Gradedtests.helloworld).text_seg;;
*)

(*

#load "_build/int64_overflow.cmo";;
#load "_build/x86/x86.cmo";;
#load "_build/simulator.cmo";;
#load "gradedtests.ml";;

open Gradedtests;;
*)
#use "util/assert.ml";;
#use "x86/x86.ml";;
#use "gradedtests.ml";;
#use "simulator.ml";;

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
in

assemble helloworld ;;

#quit;; 