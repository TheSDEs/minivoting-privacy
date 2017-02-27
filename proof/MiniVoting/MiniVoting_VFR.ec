require import FMap List Int FSet Pair Distr.
require (*  *) MiniVotingSecurity.
require (*  *) Ex_Plug_and_Pray.

clone include MiniVotingSecurity. 

(* relation that shows the result corresponds to the decryption of the board *)
module DecRelation (E: Scheme, H: HOracle.ARO): Relation ={
  proc main(stm: (pkey * pubBB * result), 
            wit: (skey * (ident * label * cipher) list)): bool ={
    var ev1, ev2, ev3, i, b, m, ubb;

     ev1 <- (stm.`2 = Publish wit.`2);
     ev2 <- (stm.`1 = extractPk wit.`1);
     i <- 0;
     ubb <- [];

     while (i < size wit.`2){
       b <- nth witness wit.`2 i;
       m  <@ E(H).dec(wit.`1, b.`2, b.`3);
       ubb <- ubb ++ [(b.`1, m)];
       i  <- i + 1;
     }

     ev3 <- (support (Rho ubb) stm.`3);
     return (ev1 /\ ev2 /\ ev3);
  }
}. 


(* the voting scheme has no verifiabiliy, thus the relation returns true *) 
module NoRelation (E: Scheme, H: HOracle.ARO) ={
  proc main(stm: (pkey * pubBB * result), 
            wit: (skey * (ident * label * cipher) list)): bool ={
     return true;
  }
}.

section VotingFriendlyRelation.
 
declare module G: GOracle.Oracle
                   { BP, BS, HRO.RO}.
declare module S: Simulator
                   { BP, BS, HRO.RO, G}.
declare module Ve: Verifier
                   { BP, HRO.RO, G, S}.
declare module P: Prover
                   { BP, HRO.RO, G, S, Ve}.
declare module C: ValidInd
                   { BP, BS, HRO.RO, G, S, Ve, P}.
declare module A: BPRIV_Adv
                   { BP, BS, HRO.RO, G, S, Ve, P, C}.
declare module E: Scheme
                   {BP, BS, HRO.RO, G, S, Ve, P, C, A}.

(* ** ASSUMPTIONS ** *)
(* ** start *)
  (* lossless assumptions *)
  axiom Aa1_ll (O <: BPRIV_Oracles{A}):
    islossless O.vote =>
    islossless O.cast =>
    islossless O.board =>
    islossless O.h => 
    islossless O.g => 
    islossless A(O).a1.

  axiom So_ll: islossless S.o.
  axiom Si_ll: islossless S.init.

  axiom Go_ll: islossless G.o.
  axiom Gi_ll: islossless G.init.

  axiom Co_ll (H <: HOracle.ARO):
    islossless H.o =>
    islossless C(H).validInd.

  axiom Ed_ll (H<:HOracle.ARO):
    islossless H.o=>
    islossless E(H).dec.

  axiom Ee_ll (H<:HOracle.ARO):
    islossless H.o=>
    islossless E(H).enc.

  (* axiom for result distribution *)
  axiom Rho_weight (x: (ident * vote option) list):
    weight (Rho x) = 1%r. 

  (* axiom for stating that the keys are generated *)
  axiom Ekgen_extractPk (H<: HOracle.ARO):
    phoare [E(H).kgen : true ==> 
          res.`1 = extractPk res.`2 ] = 1%r.

  (* axiom for linking E.dec to dec_cipher operator *)
  axiom Edec_Odec (ge: (glob E)) (sk2: skey)(l2: label) (c2: cipher):
    phoare [E(HRO.RO).dec:  
           (glob E) =ge /\ arg = (sk2, l2, c2) 
           ==>   
           (glob E) =ge /\
           res = dec_cipher sk2 l2 c2 HRO.RO.m ] = 1%r.
(* ** end *)

(* Lemma bounding voting friendly relation DecRelation *) 
lemma bound_vfr (G<: GOracle.Oracle {A, BP, BS, HRO.RO}) &m:
  islossless G.init =>
  islossless G.o =>
  Pr[VFR(E, BVFR(MV(E, P, Ve, C), A), 
         DecRelation(E), HRO.RO, G).main() @ &m : res] = 0%r.
proof.
  move => Gi Go.
  byphoare =>//=.
  proc.
 
  inline DecRelation(E, HRO.RO).main
  BVFR(MV(E, P, Ve, C), A, HRO.RO, G).main.
  wp.  
  phoare split ! 1%r 1%r =>//=.
 
  (* goal 1: lossless *)
    auto.
    while(true) (size wit.`2 -i1); progress. 
      wp; call (Ed_ll HRO.RO HRO.RO_o_ll).
      by auto; progress; smt.
    auto.
    while(true) (size bb -i); progress. 
      wp; call (Ed_ll HRO.RO HRO.RO_o_ll).
      by auto; progress; smt.
    wp.
    call (Aa1_ll (<: BVFR(MV(E, P, Ve, C), A, 
                          HRO.RO, G).L) _ _ _ _ _).
    + proc.
      if =>//=.
      if =>//=; last by auto.
      inline *.
      wp; call (Co_ll HRO.RO HRO.RO_o_ll).
      wp; while(true) (size bb - i); progress.
        by auto; progress; smt. 
      wp; call (Ee_ll HRO.RO HRO.RO_o_ll).
      wp; call (Ee_ll HRO.RO HRO.RO_o_ll).
      by auto; progress; smt.
    + proc.
      if =>//=.
      inline *; wp.
      call (Co_ll HRO.RO HRO.RO_o_ll).
      wp; while(true) (size bb - i); progress.
        by auto; progress; smt. 
      by auto; progress; smt.
    + proc; inline*; auto.
    + exact HRO.RO_o_ll. 
    + exact Go.
    while (true) (part - i0); progress.
      by auto; progress; smt.
    auto; call{1} (Ekgen_extractPk HRO.RO).
    call Gi. 
    call(_: true).
      while(true) (card work); progress.   
        by auto; progress; smt.  
      by auto; progress; smt.  
    by auto; progress; smt.

  (* goal 2: result *)
  auto.
  while{1} (0 <= i1 <= size wit.`2 /\ 
              ubb0 = map (fun (b: ident * label * cipher) =>
                       (b.`1, (dec_cipher wit.`1 b.`2 b.`3 HRO.RO.m)))
                    (take i1 wit.`2))
             (size wit.`2 - i1); progress. 
    wp; sp. 
    exists* (glob E), wit.`1, b0; elim * => ge sk2 b2. 
    call{1} (Edec_Odec ge sk2 b2.`2 b2.`3).
    by auto; progress; smt. 
  auto.
  while{1} (0 <= i <= size bb /\ 
              ubb = map (fun (b: ident * label * cipher) =>
                       (b.`1, (dec_cipher BS.sk b.`2 b.`3 HRO.RO.m)))
                    (take i bb))
             (size bb - i); progress. 
    wp; sp. 
    exists* (glob E), BS.sk, b; elim * => ge sk2 b2. 
    call{1} (Edec_Odec ge sk2 b2.`2 b2.`3).
    by auto; progress; smt. 

  wp.
  call (_: BP.pk = extractPk BS.sk).
    + exact Aa1_ll.
    + proc.
      if =>//=.
      if =>//=; last by auto.
      inline *.
      wp; call (Co_ll HRO.RO HRO.RO_o_ll).
      wp; while(true) (size bb - i); progress.
        by auto; progress; smt. 
      wp; call (Ee_ll HRO.RO HRO.RO_o_ll).
      wp; call (Ee_ll HRO.RO HRO.RO_o_ll).
      by auto; progress; smt.
    + proc.
      if =>//=.
      inline *; wp.
      call (Co_ll HRO.RO HRO.RO_o_ll).
      wp; while(true) (size bb - i); progress.
        by auto; progress; smt. 
      by auto; progress; smt.
    + proc; inline*; auto.
    + proc; auto. 
    + conseq Go. 
  while (true) (part - i0); progress.
    by auto; progress; smt.
  auto; call (Ekgen_extractPk HRO.RO).
  call Gi. 
  call(_: true).
    while(true) (card work); progress.   
      by auto; progress; smt.  
    by auto; progress; smt. 
  auto; progress; expect 9; by smt.
qed.

(* application to random oracle G *)
lemma bound_vfr_left &m:
  Pr[VFR(E, BVFR(MV(E, P, Ve, C), A), DecRelation(E), HRO.RO, G).main() @ &m : res] = 0%r.
proof.
  by rewrite (bound_vfr G &m Gi_ll Go_ll). 
qed.

(* application to simulator S *)
lemma bound_vfr_right &m:
  Pr[VFR(E, BVFR(MV(E, P, Ve, C), A), DecRelation(E), HRO.RO, S).main() @ &m : res] = 0%r.
proof.
  by rewrite (bound_vfr S &m Si_ll So_ll). 
qed.

(* Lemma bounding voting friendly relation NoRelation  *) 
lemma bound2_vfr (G<: GOracle.Oracle {A, BP, BS, HRO.RO}) &m:
  islossless G.init =>
  islossless G.o =>
  Pr[VFR(E, BVFR(MV(E, P, Ve, C), A), NoRelation(E), HRO.RO, G).main() @ &m : res] = 0%r.
proof.
  move => Gi Go.
  byphoare =>//=.
  proc.
  inline *; wp.
  by hoare =>//=.
qed.

end section VotingFriendlyRelation.