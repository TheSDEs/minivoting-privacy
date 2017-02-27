require import Option List.
require (*  *) MiniVoting_VFR DiffieHellman.
require import Distr NewDistr Perms Int FMap FSet Real Pair Mu_mem. 
require import LeftOrRight.

(* ###############################################################
   Basic election scheme with mix-nets and true identities,
   obtain from MiniVoting with 
   -1. the label (Flabel)   = empty
   -2. Publish              = empty
   -3. tally operator (Rho) = multiset over the first vote of a voter
   -4. relation (R)         = true
   -5. ValidInd             = true
   ############################################################### *)

  type ident, vote, cipher.
(* ---------------------------------------------------------------------- *)
(* 1. Flabel: empty *)
  type label = unit. 
  const lblx: label.
  op Flabel(id: ident)= lblx.

(* ---------------------------------------------------------------------- *)
(* 2. Publish: empty  *)
  type pubBB = unit.
  const pubb: pubBB.
  op Publish (bb: (ident * label * cipher) list) = pubb.

(* ---------------------------------------------------------------------- *)
(* 3. Rho: multiset (first vote policy)   *)

  (* last vote policy *) 
  op last_vote['a] (bb : (ident * 'a) list) =
  with bb = "[]"      => []
  with bb = (::) b bb => if   has (Fun.(\o) (pred1 b.`1) fst) bb
                         then last_vote bb
                         else b :: last_vote bb.

 (* remove non-valid votes *)
  op removeInvalid  (ubb: (ident * vote option) list) =
   with ubb = "[]"         => []
   with ubb = (::) idv ubb => if idv.`2 = None
                              then removeInvalid ubb
                              else (idv.`1, oget idv.`2) :: removeInvalid ubb.
  (* first vote policy *)
  op Policy['a] (bb : (ident * 'a) list) = rev(last_vote (rev bb)).

(* Rho operator: list of first valid votes:*)
  op Rho (ubb:(ident * vote option) list)  : (vote list) distr 
      = if (removeInvalid ubb = []) then MUnit.dunit []
        else MUniform.duniform (allperms (map snd (Policy (removeInvalid ubb)))).

clone export MiniVoting_VFR as Basic  with
  type ident  <- ident,
  type vote   <- vote,
  type cipher <- cipher,
  type label  <- label,              
  type pubBB  <- pubBB,             
  type result <- vote list,        
  op validInd <- (fun x y ro => true), 
  op Rho      <- Rho.

(* 5. ValidInd : do nothing *)
module ValidNothing(H: HOracle.ARO) = {
  proc validInd( b: (ident * unit * cipher), pk: pkey): bool ={
    return true;
  }
}.

(* ---------------------------------------------------------------------- *)
(* Basic Election Scheme *) 
module BasicScheme (E: Scheme, Pz: Prover,  Vz: Verifier,
                    H: HOracle.ARO,   G: GOracle.ARO)  
    = MV(E, Pz, Vz, ValidNothing, H, G).

(* ---------------------------------------------------------------------- *)
lemma sf (x: (ident * vote option) list):
  x <> [] =>
  weight (MUniform.duniform x) = 1%r. 
proof.
  move => Hx. smt. qed.
 
lemma sd (x: (ident * vote option) list):
  x = [] =>
  weight (MUnit.dunit x) = 1%r by smt.

lemma df (x: (ident * vote option) list):
  removeInvalid x <> [] =>
  map snd (Policy (removeInvalid x)) <> [].
proof. 
  have Hy: forall (y: (ident * vote) list), 
           y <>[] => map snd y <> [] by smt.
  have Hz: forall (z: (ident * vote) list),
           z <>[] => rev (last_vote z) <> [].
    by elim =>//=; smt.
  move => Hr.
  by rewrite (Hy (rev (last_vote (rev (removeInvalid x)))) 
                 (Hz (rev (removeInvalid x)) _)); first by smt.
qed.

lemma sds (x:'a list) (z: 'a):
  mem x z = true => x <> [].
proof. 
  by elim: x =>//=.
qed.

lemma ddg (x: vote list):
  x <> [] =>
  allperms x <> [].
proof.
  move => fx. 
  cut t:= allpermsP x x.
  cut t2: (perm_eq x x ) = true.
    rewrite /perm_eq//=.  
    rewrite (allP (fun (_ : vote) => true) (x ++ x)) //=. 
  move: t; rewrite t2; move => t.
  rewrite -eq_iff in t.
  by rewrite (sds (allperms x) x).
qed.

lemma Rho_weight (x : (ident * vote option) list):
   weight (Rho x) = 1%r. 
proof.
  cut t:= MUniform.duniform_ll (allperms (map snd (Policy (removeInvalid x)))).
  rewrite /is_lossless in t.
  rewrite /Rho.
  case (removeInvalid x = []).
    by rewrite (MUnit.dunitE predT).
  move => Hx.
  rewrite /weight.  
  rewrite (MUniform.duniform_ll) //=.
  have Hy: map snd (Policy (removeInvalid x)) <> []
    by rewrite (df x Hx).
  by rewrite (ddg _ Hy).
qed.


(* BPRIV PROPERTY *) 
(* --------------------------------------------------------------------------*)
section BPRIV.

declare module G : GOracle.Oracle 
                   { BP, BS, BPS, BIND, HRO.RO}.
declare module E : Scheme        
                   { BP, BS, BPS, BSC, BIND, HRO.RO, G, BSCorr,
                     PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv, BPRIV_SB, BIND2}.
declare module S : Simulator 
                   { BP, BS, BPS, BSC, BIND, HRO.RO, G, E, BSCorr,
                     BPRIV_SB, BIND2, PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv}.
declare module Vz: Verifier
                   { BP, BS, BPS, BSC, BSCorr, BIND, HRO.RO, G, E, S}.
declare module Pz : Prover
                   { BP, BS, BPS, BSC, BSCorr, BIND, HRO.RO, G, E, S, Vz}.
declare module A: BPRIV_Adv        
                  { BP, BS, BPS, BSC, HRO.RO, G, E, S, Vz, Pz, PKEvf.H.Count, 
                    PKEvf.H.HybOrcl, WrapAdv, BSCorr, BPRIV_SB, BIND, BIND2}.

(* ** ASSUMPTIONS ** *)
(* ** start *)
  (* at least 2 distinct votes *)
  axiom v_distinct: v_def_0 <> v_def_1.

  (* lossless *)
  axiom Gi_ll: islossless G.init.
  axiom Go_ll: islossless G.o.

  axiom Aa1_ll (O <: BPRIV_Oracles { A }):
    islossless O.vote    =>
    islossless O.cast    =>
    islossless O.board   =>
    islossless O.h          =>
    islossless O.g          =>
    islossless A(O).a1.
  axiom Aa2_ll (O <: BPRIV_Oracles { A }):
    islossless O.board =>
    islossless O.h         =>
    islossless O.g         =>
    islossless A(O).a2.

  axiom AC_ll (AS <: SCorr_Adv') 
            (V<: VotingScheme{AS}) 
            (O <: SCorr_Oracle {AS}):
    islossless O.h => 
    islossless O.g => 
    islossless O.test =>
    islossless AS(V,O).main.

  axiom Pp_ll (G <: GOracle.ARO): 
    islossless G.o =>
    islossless Pz(G).prove. 
  axiom Vv_ll (G <: GOracle.ARO):
    islossless G.o =>
    islossless Vz(G).verify.

  axiom Ek_ll (H <: HOracle.ARO): 
    islossless H.o =>
    islossless E(H).kgen.
  axiom Ee_ll(H <: HOracle.ARO): 
    islossless H.o =>
    islossless E(H).enc.
  axiom Ed_ll(H <: HOracle.ARO): 
    islossless H.o =>
    islossless E(H).dec.

  axiom Si_ll: islossless S.init.
  axiom So_ll: islossless S.o.
  axiom Sp_ll: islossless S.prove.

  axiom Vval_ll (V<: VotingScheme) 
                (H<: HOracle.ARO) (G<:GOracle.ARO) :
    islossless H.o =>
    islossless G.o =>
    islossless V(H,G).valid.  

  axiom Vvot_ll (V<: VotingScheme) 
                (H<: HOracle.ARO) (G<:GOracle.ARO) :
    islossless H.o =>
    islossless G.o =>
    islossless V(H,G).vote. 

  (* axiom for stating that the keys are generated (two-sided) *)
  axiom Ekgen_extractPk (H<: HOracle.ARO):
    equiv [E(H).kgen ~ E(H).kgen:  ={glob H, glob E} ==> 
          ={glob H, glob E,  res} /\ 
          res{1}.`1 = extractPk res{1}.`2  /\
          res{1}.`1 = extractPk res{1}.`2 ].

  (* axiom for stating that the keys are generated (one-sided)*)
  axiom Ekgen_extractPkL (H<: HOracle.ARO):
    phoare [E(H).kgen: true 
           ==>   
           res.`1 = extractPk res.`2 ] = 1%r.

  (* axiom for linking E.dec to dec_cipher operatorAxiom for linking E.dec to dec_cipher op *)  
  axiom Edec_Odec (ge: (glob E)) (sk2: skey)(l2: unit) (c2: cipher):
    phoare [E(HRO.RO).dec:  (glob E) =ge /\ 
           arg = (sk2, l2, c2) 
           ==>   
           (glob E) =ge /\
           res = dec_cipher sk2 l2 c2 HRO.RO.m ] = 1%r.

  (* axiom on the state of the encryption scheme E *)
  axiom Ee_eq (ge: (glob E)):
    phoare [E(HRO.RO).enc: (glob E) = ge ==> (glob E) = ge ] = 1%r.
    
  (* axiom for transforming an encryption into decryption (two-sided) *)
  axiom Eenc_dec (sk2: skey) (pk2: pkey) (l2: unit) (p2: vote): 
    (pk2 = extractPk sk2) =>
    equiv [E(HRO.RO).enc ~ E(HRO.RO).enc : 
          ={glob HRO.RO, glob E, arg} /\ arg{1}=( pk2, l2, p2)   
          ==> 
          ={glob HRO.RO, glob E,  res} /\ 
          Some p2 = dec_cipher sk2 l2 res{1} HRO.RO.m{1} ].
     
  (* axiom for transforming an encryption into decryption (one-sided) *)
  axiom Eenc_decL (ge: (glob E)) (sk2: skey) 
                 (pk2: pkey)(l2: unit) (p2: vote): 
    (pk2 = extractPk sk2) =>
    phoare [E(HRO.RO).enc : (glob E) = ge /\ arg=( pk2, l2, p2)
          ==> 
          (glob E) = ge /\ 
          Some p2 = dec_cipher sk2 l2 res HRO.RO.m ]= 1%r.         
(* ** end *)

(* lossless for Strong consistency Op *)
local lemma Co_ll (H <: HOracle.ARO):
  islossless H.o =>
  islossless ValidNothing(H).validInd.
proof.
  move => Ho; by proc; auto.
qed.

(* lemma for vfr is 0 for this relation *) 
local lemma bound_vfr (Gx <: GOracle.Oracle{BS, BP, HRO.RO, A, E}) &m:
  islossless Gx.init =>
  islossless Gx.o => 
  Pr[VFR(E,BVFR(MV(E,Pz,Vz,ValidNothing), A), 
         NoRelation(E), HRO.RO, Gx).main() @ &m : res] = 0%r.
proof.
  move => Gxi Gxo.
  byphoare =>//=.
  proc; inline*; wp.
  by hoare =>//=.
qed.

(* lemma on a voting relation that does not 
     change the state of the eager random oracle *)
local lemma relCons (gh : (glob HRO.RO)):
    phoare[ NoRelation(E, HRO.RO).main :
             (glob HRO.RO) = gh ==> (glob HRO.RO) = gh] = 1%r.
proof.
  by proc.
qed.

(* lemma on encryption implies validInd *)
local lemma enc_to_validInd (pkx: pkey) (id: ident) (v: vote) (l : unit):
  equiv[E(HRO.RO).enc ~ E(HRO.RO).enc: 
         ={glob HRO.RO, glob E, arg} /\ arg{1} = (pkx,l,v) 
         ==> 
         ={res, glob E, glob HRO.RO} /\
         true].
proof.
  by sim.
qed.

(* lemma on transforming C.validInd in validInd operator *)
local lemma validInd_ax (gc : (glob ValidNothing)) (pk : pkey) 
                  (b : ident * unit * cipher):
  phoare[ ValidNothing(HRO.RO).validInd :
           (glob ValidNothing) = gc /\ arg = (b, pk) ==>
           (glob ValidNothing) = gc /\ res = true] = 1%r
  by proc.

(* bound on the scorr in bpriv by ind1cca *)
lemma scorr_bpriv (LR<: LorR { BS, BP, BIND, BIND2, BSCorr, BSC, 
                                     HRO.RO, A, E, Vz, Pz, S}) &m:
  Pr[SCorr(MV(E, Pz, Vz, ValidNothing), 
           BSCorr(MV(E, Pz, Vz, ValidNothing), A, LR), 
           HRO.RO, S).main() @ &m : BSC.valid]
  = 
`|Pr[Ind1CCA(E,INDB(Bmem(MV(E, Pz, Vz, ValidNothing), 
                         BSCorr(MV(E,Pz,Vz, ValidNothing),A, LR), S, HRO.RO)),
             HRO.RO,Left).main() @ &m: res /\  size BS.encL <= 1] -
  Pr[Ind1CCA(E,INDB(Bmem(MV(E, Pz, Vz, ValidNothing),
                         BSCorr(MV(E,Pz,Vz, ValidNothing),A, LR), S, HRO.RO)),
             HRO.RO,Right).main() @ &m: res /\  size BS.encL <= 1]|. 
proof. 
  by rewrite (scorr_bpriv E S Vz Pz ValidNothing A v_distinct enc_to_validInd 
              validInd_ax Eenc_decL Eenc_dec Edec_Odec Ekgen_extractPk Ekgen_extractPkL 
              Ek_ll Ee_ll Ed_ll So_ll Si_ll AC_ll LR &m). 
qed.

(* FIXME: change SCorrbound to IND-1CCA bound *)
lemma bpriv  &m:
  `|Pr[BPRIV_L(BasicScheme (E, Pz, Vz), A, HRO.RO, G).main() @ &m : res] -
    Pr[BPRIV_R(BasicScheme (E, Pz, Vz), A, HRO.RO, G, S).main() @ &m : res]| 
<=
  `|Pr[ZK_L(NoRelation(E,HRO.RO),
            Pz, BZK(E, Pz, ValidNothing, Vz, A, HRO.RO), G).main() @ &m : res] -
    Pr[ZK_R(NoRelation(E,HRO.RO),
            S, BZK(E, Pz, ValidNothing, Vz, A, HRO.RO)).main() @ &m : res]| +
 n%r *
  `|Pr[Ind1CCA(E,INDB(Bmem(MV(E, Pz, Vz, ValidNothing), 
                         BSCorr(MV(E,Pz,Vz, ValidNothing),A, Left), S, HRO.RO)),
               HRO.RO,Left).main() @ &m: res /\  size BS.encL <= 1] -
    Pr[Ind1CCA(E,INDB(Bmem(MV(E, Pz, Vz, ValidNothing),
                         BSCorr(MV(E,Pz,Vz, ValidNothing),A, Left), S, HRO.RO)),
               HRO.RO,Right).main() @ &m: res /\  size BS.encL <= 1]| +
 n%r *
  `|Pr[Ind1CCA(E,INDB(Bmem(MV(E, Pz, Vz, ValidNothing), 
                         BSCorr(MV(E,Pz,Vz, ValidNothing),A, Right), S, HRO.RO)),
                HRO.RO,Left).main() @ &m: res /\  size BS.encL <= 1] -
    Pr[Ind1CCA(E,INDB(Bmem(MV(E, Pz, Vz, ValidNothing),
                         BSCorr(MV(E,Pz,Vz, ValidNothing),A, Right), S, HRO.RO)),
               HRO.RO,Right).main() @ &m: res /\  size BS.encL <= 1]| +
 n%r *
  `|Pr[Ind1CCA(E, WrapAdv(BIND(MV(E, Pz, Vz, ValidNothing), A, S), E, HRO.RO), HRO.RO, Left).main
         () @ &m : res /\ WrapAdv.l <= n /\ size BS.encL <= 1] -
    Pr[Ind1CCA(E, WrapAdv(BIND(MV(E, Pz, Vz, ValidNothing), A, S), E, HRO.RO), HRO.RO, Right).main
         () @ &m : res /\ WrapAdv.l <= n /\ size BS.encL <= 1]|.
proof.
  have ->: Pr[BPRIV_L(BasicScheme (E, Pz, Vz), A, HRO.RO, G).main() @ &m : res] =
           Pr[BPRIV_L(MV(E, Pz, Vz, ValidNothing), A, HRO.RO, G).main() @ &m : res].
    by byequiv=>//=; sim.
  have ->: Pr[BPRIV_R(BasicScheme (E, Pz, Vz), A, HRO.RO, G, S).main() @ &m : res] =
           Pr[BPRIV_R(MV(E, Pz, Vz, ValidNothing), A, HRO.RO, G, S).main() @ &m : res].
    by byequiv=>//=; sim.
  (* use bound on bpriv for MiniVoting *) print bpriv.
  cut oldbpriv := (bpriv G E S Vz Pz NoRelation ValidNothing A  Gi_ll Go_ll Aa1_ll Aa2_ll Pp_ll 
                    Vv_ll Ek_ll Ee_ll Ed_ll Si_ll So_ll Sp_ll Co_ll Vval_ll Vvot_ll 
                    relCons Rho_weight Ekgen_extractPk Edec_Odec 
                    Ee_eq Eenc_decL Eenc_dec &m).
  (* make VFR experiment 0 *)
  rewrite (bound_vfr G &m Gi_ll Go_ll) (bound_vfr S &m Si_ll So_ll) in oldbpriv.
  (* make scorr bound to IND-1-CCA bound *)
  by rewrite (scorr_bpriv Left &m) (scorr_bpriv Right &m) in oldbpriv.
qed.

end section BPRIV.

section Consistency.

declare module H : HOracle.Oracle 
                   { BP}.
declare module G : GOracle.Oracle 
                   { BP, HRO.RO, H}.
declare module E : Scheme        
                   { BP, H, G, HRO.RO}.
declare module S : Simulator 
                   { HRO.RO, H, G, E}.
declare module Ve: Verifier
                   { HRO.RO, H, G, E, S}.
declare module P : Prover
                   { HRO.RO, H, G, E, S, Ve}.
declare module AC2: SConsis2_Adv {BP, H, HRO.RO, G, E}.
declare module AC3: SConsis3_Adv {BP, H, E, G, P}.

(* ** ASSUMPTIONS ** *)
(* ** start *)
  axiom Gi_ll: islossless G.init.
  axiom Go_ll: islossless G.o.

  axiom Pp_ll (G <: GOracle.ARO): 
    islossless G.o =>
    islossless P(G).prove. 

  axiom Ek_ll (H <: HOracle.ARO): 
    islossless H.o =>
    islossless E(H).kgen.

  axiom AC2_ll (O <: SCons_Oracle { AC2 }):
    islossless O.h       =>
    islossless O.g       =>
    islossless AC2(O).main.
(* ** end *)

local lemma Co_ll (H <: HOracle.ARO):
  islossless H.o =>
  islossless ValidNothing(H).validInd.
proof.
  move => Ho; proc; auto.
qed.

local lemma validInd_ax (gc: (glob ValidNothing)) (pk: pkey) (b: ident * unit * cipher):
  phoare[ ValidNothing(HRO.RO).validInd: (glob ValidNothing) = gc /\ arg = (b, pk) ==>
          (glob ValidNothing) = gc /\
          res = true] = 1%r
  by proc.


lemma consis1(id: ident, v: vote, l: unit) &m: 
   Pr[SConsis1(BasicScheme(E,P,Ve), CE(E), H, G).main(id,v, l) @ &m: res]  >=
   Pr[PKEvf.Correctness(E, H).main(v,l) @ &m: res].
proof.
  have ->: Pr[SConsis1(BasicScheme(E,P,Ve), CE(E), H, G).main(id,v, l) @ &m: res] =
           Pr[SConsis1(MV(E,P,Ve,ValidNothing), CE(E), H, G).main(id,v, l) @ &m: res].
    by byequiv =>//=; sim.
  by rewrite (consis1 H G E S Ve P ValidNothing AC2 AC3 Gi_ll Go_ll 
                      Co_ll Pp_ll Ek_ll AC2_ll Rho_weight validInd_ax id v l &m).
qed.


lemma consis2 &m: 
  Pr[SConsis2(BasicScheme(E,P,Ve), ValidNothing, AC2, HRO.RO, G).main() @ &m: res] = 1%r.
proof.

  have ->:Pr[SConsis2(BasicScheme(E,P,Ve), ValidNothing, AC2, HRO.RO, G).main() @ &m: res] =
          Pr[SConsis2(MV(E, P, Ve, ValidNothing), ValidNothing, AC2, HRO.RO, G).main() @ &m: res].
    by byequiv =>//=; sim.
  by rewrite (consis2 H G E S Ve P ValidNothing AC2 AC3 Gi_ll Go_ll 
                      Co_ll Pp_ll Ek_ll AC2_ll Rho_weight validInd_ax &m).
qed.

equiv consis3 &m:
    SConsis3_L(BasicScheme(E,P,Ve), ValidNothing, AC3, H, G).main ~ 
    SConsis3_R(BasicScheme(E,P,Ve), CE(E), ValidNothing, AC3, H, G).main
    : ={glob H, glob G, glob E, glob ValidNothing, glob AC3} ==> ={res}. 
proof.

  progress.
  cut t:= (consis3 H G E S Ve P ValidNothing AC2 AC3 Gi_ll Go_ll 
                      Co_ll Pp_ll Ek_ll AC2_ll Rho_weight validInd_ax &m).

  transitivity SConsis3_L(MV(E, P, Ve, ValidNothing), ValidNothing, AC3, H, G).main
  (={glob H, glob G, glob E, glob ValidNothing, glob AC3} ==> ={res})
  (={glob H, glob G, glob E,  glob ValidNothing, glob AC3} ==> ={res})=>//=.
  + progress; smt. 
  + proc. 
    seq 10 10 : (={ glob H, glob G, glob E, glob ValidNothing, glob AC3, BP.sk, bb, ev, r}). 
      by sim. 
    if =>//=; auto.
    inline *.
    wp; call{1} (Pp_ll G Go_ll); call{2} (Pp_ll G Go_ll).
    sim.
   

  transitivity SConsis3_R(MV(E, P, Ve, ValidNothing), CE(E), ValidNothing, AC3, H, G).main
  (={glob H, glob G, glob E, glob ValidNothing, glob AC3} ==> ={res})
  (={glob H, glob G, glob E, glob ValidNothing, glob AC3} ==> ={res})=>//=.
  + progress; smt. 
  by sim. 
qed.

end section Consistency.

section Correctness.
declare module E : Scheme        
                   { BS, BP, BSC, BSCorr, HRO.RO}.
declare module S : Simulator 
                   { BSC, BSCorr, BP, BS, HRO.RO, E}.
declare module Ve: Verifier
                   { BS, BP, BSCorr, HRO.RO, E, S}.
declare module Pe : Prover
                   { BS, BP, BSCorr, HRO.RO, E, S, Ve}.

declare module A: BPRIV_Adv { BSC, BS, BSCorr, BP, S, Pe, Ve, E, HRO.RO}.

(* ** ASSUMPTIONS ** *)
(* ** start *)
  (* at least 2 distinct votes *)
  axiom v_distinct: v_def_0 <> v_def_1.

  (* lossless *)
  axiom So_ll: islossless S.o.
  axiom Si_ll: islossless S.init.

  axiom Ek_ll(H <: HOracle.ARO): 
    islossless H.o =>
    islossless E(H).kgen.
  axiom Ee_ll(H <: HOracle.ARO): 
    islossless H.o =>
    islossless E(H).enc.
  axiom Ed_ll(H <: HOracle.ARO): 
    islossless H.o =>
    islossless E(H).dec.

  axiom AC_ll (AS <: SCorr_Adv') 
              (V<: VotingScheme{AS}) (O <: SCorr_Oracle {AS}):
    islossless O.h => 
    islossless O.g => 
    islossless O.test =>
    islossless AS(V,O).main.

  (* axiom for transforming an encryption into decryption (one-sided) *)
  axiom Eenc_decL (ge: (glob E)) (sk2: skey) 
                 (pk2: pkey)(l2: unit) (p2: vote): 
    (pk2 = extractPk sk2) =>
    phoare [ E(HRO.RO).enc : (glob E) = ge /\ arg=( pk2, l2, p2)
          ==> 
          (glob E) = ge /\ 
          Some p2 = dec_cipher sk2 l2 res HRO.RO.m ]= 1%r.

  (* axiom for transforming an encryption into decryption (two-sided) *)
  axiom Eenc_dec (sk2: skey) (pk2: pkey) (l2: unit) (p2: vote): 
    (pk2 = extractPk sk2) =>
    equiv [ E(HRO.RO).enc ~ E(HRO.RO).enc : 
          ={glob HRO.RO, glob E, arg} /\ arg{1}=( pk2, l2, p2)   
          ==> 
          ={glob HRO.RO, glob E,  res} /\ 
          Some p2 = dec_cipher sk2 l2 res{1} HRO.RO.m{1} ].

  (* axioma linking E.dec to dec_cipher operator  *)
  axiom Edec_Odec (ge: (glob E))
                (sk2: skey)(l2: unit) (c2: cipher):
    phoare [ E(HRO.RO).dec:  (glob E) =ge /\ 
           arg = (sk2, l2, c2) 
           ==>   
           (glob E) =ge /\
           res = dec_cipher sk2 l2 c2 HRO.RO.m ] = 1%r.

  (* axiom for stating that the keys are generated (two-sided) *)
  axiom Ekgen_extractPk (H<: HOracle.ARO):
    equiv [ E(H).kgen ~ E(H).kgen:  ={glob H, glob E} ==> 
          ={glob H, glob E,  res} /\ 
          res{1}.`1 = extractPk res{1}.`2  /\
          res{1}.`1 = extractPk res{1}.`2 ].

  (* axiom for stating that the keys are generated (one-sided) *)
  axiom Ekgen_extractPkL (H<: HOracle.ARO):
    phoare [ E(H).kgen: true 
           ==>   
           res.`1 = extractPk res.`2 ] = 1%r.
(* ** end *)

(* lemma for encryption always implies validInd true *)
local lemma enc_to_validInd (pk: pkey) (id: ident) (v: vote) (l : unit):
  equiv[ E(HRO.RO).enc ~ E(HRO.RO).enc: 
          ={glob HRO.RO, glob E, arg} /\ arg{1} = (pk,l,v)
         ==> ={res, glob E, glob HRO.RO} /\
          true].
proof.
  by sim.
qed.

(* validInd operator = validInd function *)
local lemma validInd_ax (gc: (glob ValidNothing)) (pk: pkey) (b: ident * unit * cipher):
    phoare[ ValidNothing(HRO.RO).validInd: 
            (glob ValidNothing) = gc /\ arg = (b, pk) 
            ==>
            (glob ValidNothing) = gc /\ res = true] = 1%r
  by proc.


lemma scorr_bound (AS <: SCorr_Adv' { E, Pe, Ve, HRO.RO, BSC, BS}) 
                  (G  <: GOracle.Oracle { BS, BP, BSC, BSCorr, HRO.RO, E, Pe, Ve, AS}) &m:
islossless G.init =>
islossless G.o =>
  Pr[SCorr(BasicScheme(E,Pe,Ve), 
           AS(BasicScheme(E,Pe,Ve)), HRO.RO, G).main() @ &m: BSC.valid ] = 
`|Pr[Ind1CCA(E,INDB(Bmem(MV(E, Pe, Ve, ValidNothing), 
                         AS(MV(E, Pe, Ve, ValidNothing)), G, HRO.RO)),
             HRO.RO,Left).main()  @ &m: res /\  size BS.encL <= 1] -
  Pr[Ind1CCA(E,INDB(Bmem(MV(E, Pe, Ve, ValidNothing), 
                         AS(MV(E, Pe, Ve, ValidNothing)), G, HRO.RO)),
             HRO.RO,Right).main()  @ &m: res /\  size BS.encL <= 1]|.
proof. 

  have ->:Pr[SCorr(BasicScheme(E,Pe,Ve), 
                   AS(BasicScheme(E,Pe,Ve)), HRO.RO, G).main() @ &m: BSC.valid ] =
           Pr[SCorr(MV(E, Pe, Ve, ValidNothing), 
                    AS(MV(E,Pe,Ve,ValidNothing)), HRO.RO, G).main() @ &m: BSC.valid ].
    by byequiv =>//=; sim.
  by exact (scorr E S Ve Pe ValidNothing A v_distinct enc_to_validInd
                      validInd_ax Eenc_decL Eenc_dec 
                      Edec_Odec Ekgen_extractPk Ekgen_extractPkL Ek_ll Ee_ll Ed_ll
                      So_ll Si_ll AC_ll AS G &m).
qed.

end section Correctness.
