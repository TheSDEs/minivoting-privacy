require import Option List.
require (*  *) Helios_mix_ord DiffieHellman.
require import Distr NewDistr Perms Int FMap FSet Real Pair Mu_mem. 
require import LeftOrRight.

(* ###############################################################
   Minimal election scheme with mixnets and true identities,
   obtain from Helios_mix with 
   -1. the label (Flabel)   = empty
   -2. Publish              = empty
   -3. tally operator (Rho) = multiset over the first vote of a voter
   -4. relation (R)         = true
   -5. ValidInd             = true
   ############################################################### *)

  type ident, h_cipher, h_prf, h_data, vote.

(* ---------------------------------------------------------------------- *)
(* 1. Flabel: empty *)
  type label = unit. 
  const lblx: label.
  op Flabel(id: ident)= lblx.

(* ---------------------------------------------------------------------- *)
(* 2. Publish: empty  *)
  type pubBB = unit.
  const pubb: pubBB.
  op Publish (bb: (ident * label * (h_cipher * h_prf* h_data)) list) = pubb.

(* ---------------------------------------------------------------------- *)
(* 3. Rho: multiset (first vote policy)   *)

  (* last vote policy *) 
  op last_vote['a] (bb : (ident * 'a) list) =
    with bb = "[]"      => []
    with bb = (::) b bb => if has (Fun.(\o) (pred1 b.`1) fst) bb
                           then last_vote bb
                           else b :: last_vote bb.

  (* remove non-valid votes *)
  op removeInvalid  (ubb: (ident * vote option) list) =
    with ubb = "[]"         => []
    with ubb = (::) idv ubb => if idv.`2 = None
                              then removeInvalid ubb
                              else (idv.`1, oget idv.`2) :: removeInvalid ubb.

  (* keep first vote policy *)
  op Policy['a] (bb : (ident * 'a) list) = rev (last_vote (rev bb)).

  (* Rho operator, defined in Helios_mix_ord *)
clone export Helios_mix_ord as Basic  with
  type ident    <- ident,
  type vote     <- vote,
  type h_data   <- h_data,
  type h_cipher <- h_cipher,
  type h_prf    <- h_prf,
  type label    <- label,              
  type pubBB    <- pubBB,                   
  op HM.MV2.validInd <- (fun x y ro => true), (* no check for ballot consistency *)
  op HM.MV2.Flabel   <- Flabel,
  op Policy['a]  <- Policy,
  op removeInvalid <- removeInvalid. 

(* 5. ValidInd : do nothing *)
  module ValidNothing(H: HOracle.ARO) = {
    proc validInd( b: (ident * unit * cipher), pk: pkey): bool ={
      return true;
   }
  }.

(* ---------------------------------------------------------------------- *)
(* Basic Election Scheme *)  
module BasicScheme (Pe: PSpke.Prover, Ve: PSpke.Verifier, 
                    Pz: Prover,  Vz: Verifier,
                    H: HOracle.ARO,   G: GOracle.ARO)  
    =  HeliosMix(Pe, Ve, ValidNothing, Pz, Vz, H, G).

(* Security *) 
(* --------------------------------------------------------------------------*)
section Security.

declare module G : GOracle.Oracle { BS, BPS, BP, BSC, BIND, BSCorr, HRO.RO, SCorr_Oracle}.
declare module Pe: PSpke.Prover   { BS, BP, BSC, BSCorr, HRO.RO, SCorr_Oracle, BPS, BIND, G,
                                   PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv, BPRIV_SB, BIND2 }.
declare module Ve: PSpke.Verifier { BS, BP, BSC, BSCorr, Pe, HRO.RO, BPS, BIND, G,
                                   PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv, BPRIV_SB, BIND2}.
declare module S : Simulator      { BP, BS, BPS, BSC, BIND, HRO.RO, G, Pe, Ve, BSCorr,
                                   BPRIV_SB, BIND2, PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv}.
declare module Vz: Verifier       { BP, BS, BPS, BSC, BSCorr, BIND, HRO.RO, G, Pe, Ve, S}.
declare module Pz : Prover        { BP, BS, BPS, BSC, BSCorr, BIND, HRO.RO, G, Pe, Ve, S, Vz}.
declare module A: BPRIV_Adv       { BP, BS, BPS, BSC, HRO.RO, G, Pe, Ve, S, Vz, Pz, PKEvf.H.Count, 
                                  PKEvf.H.HybOrcl, WrapAdv, BSCorr, BPRIV_SB, BIND, BIND2}.
declare module AC2: SConsis2_Adv {BP, HRO.RO, G}.
declare module AC3: SConsis3_Adv {BP, HRO.RO, Pe, Ve, Pz, G}.

(* ** ASSUMPTIONS ** *)
(* ** start *)
  (* at least 2 distinct votes *)
  axiom v_distinct: v_def_0 <> v_def_1.

  (* axiom linking Ve.verify to verify operator *)
  axiom Verify_to_verify (gv: (glob Ve)) (s: h_stm) (p: h_prf):
    phoare[Ve(HRO.RO).verify: (glob Ve) = gv /\ arg = (s, p)
         ==>
         (glob Ve) = gv /\
         res = verify s p HRO.RO.m] = 1%r.

  (* axiom on state of prover *)
  axiom LPKE_prover_keepstate (gp: (glob Pe)) (H<: HOracle.ARO):
    phoare[Pe(H).prove: 
          (glob Pe) = gp ==> (glob Pe) = gp] = 1%r.

  (* axiom transforming a proof in a verification (two-sided) *)
  axiom Prover_to_verify (s: h_stm) (w: h_wit):
    equiv[Pe(HRO.RO).prove ~ Pe(HRO.RO).prove: 
         ={glob HRO.RO, glob Pe, arg} /\ arg{1} = (s, w)
         ==>
         ={glob HRO.RO, glob Pe, res} /\
         verify s res{1} HRO.RO.m{1}].

  (* axiom transforming a proof in a verification (one-sided) *)
  axiom Prover_to_verify_left (gp: (glob Pe)) (s: h_stm) (w: h_wit):
    phoare[ Pe(HRO.RO).prove: 
          (glob Pe) = gp /\ arg = (s, w)
           ==>
          (glob Pe) = gp /\ verify s res HRO.RO.m]= 1%r.

  (* lossless *)
  (* ->random oracles *)
  axiom Gi_ll: islossless G.init. 
  axiom Go_ll: islossless G.o.

  (* -> big proof system, for the one for result *)
  axiom Pz_ll (G <: GOracle.ARO):
    islossless G.o => 
    islossless Pz(G).prove.
  axiom Vz_ll (G <: GOracle.ARO):
    islossless G.o => 
    islossless Vz(G).verify.

  (* -> simulator for big proof *)
  axiom Si_ll: islossless S.init.
  axiom So_ll: islossless S.o.
  axiom Sp_ll: islossless S.prove.

  (* -> adversary calls *)
  axiom A1_ll (O <: BPRIV_Oracles{A}):
    islossless O.vote =>
    islossless O.cast =>
    islossless O.board =>
    islossless O.h => 
    islossless O.g => 
    islossless A(O).a1.
  axiom A2_ll (O <: BPRIV_Oracles{A}):
    islossless O.board =>
    islossless O.h => 
    islossless O.g => 
    islossless A(O).a2. 
  axiom AC2_ll (O <: SCons_Oracle{AC2}):
   islossless O.h => 
   islossless O.g => 
   islossless AC2(O).main.
  axiom AS_ll (AS <: SCorr_Adv') 
            (V<: VotingScheme{AS}) (O <: SCorr_Oracle {AS}):
    islossless O.h => 
    islossless O.g => 
    islossless O.test =>
    islossless AS(V,O).main.

  (* -> any voting scheme *)
  axiom Vval_ll (V<: VotingScheme) (H<: HOracle.ARO) (G<:GOracle.ARO) :
    islossless H.o =>
    islossless G.o =>
    islossless V(H,G).valid.  
  axiom Vvot_ll (V<: VotingScheme) (H<: HOracle.ARO) (G<:GOracle.ARO) :
    islossless H.o =>
    islossless G.o =>
    islossless V(H,G).vote. 

  (* -> small proof system, for the ciphertext *)
  axiom Pe_ll (H <: HOracle.ARO):
    islossless H.o => 
    islossless Pe(H).prove.
  axiom Ve_ll (H <: HOracle.ARO):
    islossless H.o => 
    islossless Ve(H).verify.
(* ** end *)

local lemma C_ll (H <: HOracle.ARO):
    islossless H.o => 
    islossless ValidNothing(H).validInd by progress;proc.

local lemma relConstraint (gh : (glob HRO.RO)):
    phoare[ NoRelation(IPKE(Pe,Ve),HRO.RO).main : 
          (glob HRO.RO) = gh ==> (glob HRO.RO) = gh] = 1%r
  by proc; auto.

local lemma enc_to_validInd (pkx: pkey) (id: ident) (v: plain) (l : label):
    equiv[IPKE(Pe,Ve,HRO.RO).enc ~ IPKE(Pe,Ve,HRO.RO).enc: 
         ={glob HRO.RO, glob IPKE(Pe,Ve), arg} /\ arg{1} = (pkx,l,v) 
         ==> ={res, glob IPKE(Pe,Ve), glob HRO.RO} /\
          true].
proof.
  proc.
  call (_: ={glob HRO.RO}); first by sim. 
  by auto; smt.
qed.

local lemma validInd_ax (gc: (glob ValidNothing)) (pk: pkey) (b: ident * label * cipher):
  phoare[ValidNothing(HRO.RO).validInd: 
         (glob ValidNothing) = gc /\ arg = (b, pk) 
          ==>
          (glob ValidNothing) = gc /\ res = true] = 1%r
  by proc.


(* vfr is 0 for this relation *) 
lemma bound_vfr (Gx <: GOracle.Oracle{BS, BP, HRO.RO, A, Pe, Ve}) &m:
  islossless Gx.init =>
  islossless Gx.o => 
  Pr[VFR(IPKE(Pe,Ve),BVFR(MV(IPKE(Pe,Ve),Pz,Vz,ValidNothing), A), 
         NoRelation(IPKE(Pe,Ve)), HRO.RO, Gx).main() @ &m : res] = 0%r.
proof.
  move => Gxi Gxo.
  byphoare =>//=.
  proc; inline*; wp.
  by hoare =>//=.
qed.


(* bound on the scorr in bpriv by ind1cca *)
lemma scorr_bpriv (LR<: LorR { BS, BP, BIND, BIND2, BSCorr, BSC, 
                                     HRO.RO, A, Pe, Ve, Vz, Pz, S}) &m:
  Pr[SCorr(HeliosMix(Pe, Ve, ValidNothing, Pz, Vz), 
           BSCorr(HeliosMix(Pe, Ve, ValidNothing, Pz, Vz), A, LR), 
           HRO.RO, S).main() @ &m : BSC.valid]
  = 
`|Pr[Ind1CCA(IPKE(Pe,Ve),
             INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, ValidNothing), 
                       BSCorr(MV(IPKE(Pe,Ve),Pz,Vz, ValidNothing),A, LR), S, HRO.RO)),
             HRO.RO,Left).main() @ &m: res /\  size BS.encL <= 1] -
  Pr[Ind1CCA(IPKE(Pe,Ve),
             INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, ValidNothing),
                       BSCorr(MV(IPKE(Pe,Ve),Pz,Vz, ValidNothing),A, LR), S, HRO.RO)),
             HRO.RO,Right).main() @ &m: res /\  size BS.encL <= 1]|. 
proof. 
  by rewrite (scorr_bpriv ValidNothing Pe Ve Pz Vz G S NoRelation A AC2 AC3 v_distinct 
            Verify_to_verify LPKE_prover_keepstate Prover_to_verify Prover_to_verify_left 
            validInd_ax Gi_ll Go_ll Pz_ll Vz_ll Si_ll So_ll Sp_ll A1_ll A2_ll AC2_ll AS_ll 
            Vval_ll Vvot_ll Pe_ll Ve_ll C_ll relConstraint enc_to_validInd LR &m).
qed.

(* FIXME: change SCorrbound to IND-1CCA bound *) 
lemma bpriv  &m:
  `|Pr[BPRIV_L(BasicScheme (Pe, Ve, Pz, Vz), A, HRO.RO, G).main() @ &m : res] -
    Pr[BPRIV_R(BasicScheme (Pe, Ve, Pz, Vz), A, HRO.RO, G, S).main() @ &m : res]| 
<=
  `|Pr[ZK_L(NoRelation(IPKE(Pe,Ve),HRO.RO),
            Pz, BZK(IPKE(Pe,Ve), Pz, ValidNothing, Vz, A, HRO.RO), G).main() @ &m : res] -
    Pr[ZK_R(NoRelation(IPKE(Pe,Ve),HRO.RO),
            S, BZK(IPKE(Pe,Ve), Pz, ValidNothing, Vz, A, HRO.RO)).main() @ &m : res]| +
 n%r *
  `|Pr[Ind1CCA(IPKE(Pe,Ve),
               INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, ValidNothing), 
                         BSCorr(MV(IPKE(Pe,Ve),Pz,Vz, ValidNothing),A, Left), S, HRO.RO)),
               HRO.RO,Left).main() @ &m: res /\  size BS.encL <= 1] -
    Pr[Ind1CCA(IPKE(Pe,Ve),
               INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, ValidNothing),
                         BSCorr(MV(IPKE(Pe,Ve),Pz,Vz, ValidNothing),A, Left), S, HRO.RO)),
               HRO.RO,Right).main() @ &m: res /\  size BS.encL <= 1]| +
 n%r *
  `|Pr[Ind1CCA(IPKE(Pe,Ve),
               INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, ValidNothing), 
                         BSCorr(MV(IPKE(Pe,Ve),Pz,Vz, ValidNothing),A, Right), S, HRO.RO)),
               HRO.RO,Left).main() @ &m: res /\  size BS.encL <= 1] -
    Pr[Ind1CCA(IPKE(Pe,Ve),
               INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, ValidNothing),
                         BSCorr(MV(IPKE(Pe,Ve),Pz,Vz, ValidNothing),A, Right), S, HRO.RO)),
               HRO.RO,Right).main() @ &m: res /\  size BS.encL <= 1]| +
 n%r *
  `|Pr[Ind1CCA(IPKE(Pe,Ve), 
               WrapAdv(BIND(MV(IPKE(Pe,Ve), Pz, Vz, ValidNothing), A, S), 
                       IPKE(Pe,Ve), HRO.RO), 
               HRO.RO, Left).main () @ &m : res /\ WrapAdv.l <= n /\ size BS.encL <= 1] -
    Pr[Ind1CCA(IPKE(Pe,Ve), 
               WrapAdv(BIND(MV(IPKE(Pe,Ve), Pz, Vz, ValidNothing), A, S), 
                       IPKE(Pe,Ve), HRO.RO), 
               HRO.RO, Right).main () @ &m : res /\ WrapAdv.l <= n /\ size BS.encL <= 1]|.
proof.
  have ->: Pr[BPRIV_L(BasicScheme (Pe, Ve, Pz, Vz), A, HRO.RO, G).main() @ &m : res] =
           Pr[BPRIV_L(HeliosMix(Pe, Ve, ValidNothing, Pz, Vz), A, HRO.RO, G).main() @ &m : res].
    by byequiv=>//=; sim.
  have ->: Pr[BPRIV_R(BasicScheme (Pe, Ve, Pz, Vz), A, HRO.RO, G, S).main() @ &m : res] =
           Pr[BPRIV_R(HeliosMix(Pe, Ve, ValidNothing, Pz, Vz), A, HRO.RO, G, S).main() @ &m :res].
    by byequiv=>//=; sim.
  (* use bound on bpriv for MiniVoting *) 
  cut := (bpriv ValidNothing Pe Ve Pz Vz G S NoRelation A AC2 AC3 v_distinct 
            Verify_to_verify LPKE_prover_keepstate Prover_to_verify Prover_to_verify_left 
            validInd_ax Gi_ll Go_ll Pz_ll Vz_ll Si_ll So_ll Sp_ll A1_ll A2_ll AC2_ll AS_ll 
            Vval_ll Vvot_ll Pe_ll Ve_ll C_ll relConstraint enc_to_validInd &m).
  (* make VFR experiment 0 *)
  by rewrite (bound_vfr G &m Gi_ll Go_ll) (bound_vfr S &m Si_ll So_ll).
qed.

(* Lemma bounding STRONG CONSITENCY *) 
lemma consis1(id: ident, v: plain, l: label) &m: 
   Pr[SConsis1(BasicScheme(Pe, Ve, Pz, Vz), 
               CE(IPKE(Pe,Ve)), HRO.RO, G).main(id,v, l) @ &m: res]  >=
   Pr[PKEvf.Correctness(IPKE(Pe,Ve), HRO.RO).main(v,l) @ &m: res].
proof.
  have ->:  Pr[SConsis1(BasicScheme(Pe, Ve, Pz, Vz), 
               CE(IPKE(Pe,Ve)), HRO.RO, G).main(id,v, l) @ &m: res] =
            Pr[SConsis1(HeliosMix(Pe, Ve, ValidNothing, Pz, Vz), 
                       CE(IPKE(Pe,Ve)), HRO.RO, G).main(id,v, l) @ &m: res].
    by byequiv =>//=; sim.

  by rewrite (consis1 ValidNothing Pe Ve Pz Vz G S NoRelation A AC2 AC3 v_distinct 
            Verify_to_verify LPKE_prover_keepstate Prover_to_verify Prover_to_verify_left 
            validInd_ax Gi_ll Go_ll Pz_ll Vz_ll Si_ll So_ll Sp_ll A1_ll A2_ll AC2_ll AS_ll 
            Vval_ll Vvot_ll Pe_ll Ve_ll C_ll relConstraint enc_to_validInd id v l &m).
qed.

lemma consis2 &m:
  Pr[SConsis2(BasicScheme(Pe, Ve, Pz, Vz), 
              ValidNothing, AC2, HRO.RO, G).main() @ &m: res] = 1%r.
proof. 
   have ->: Pr[SConsis2(BasicScheme(Pe, Ve, Pz, Vz), 
                        ValidNothing, AC2, HRO.RO, G).main() @ &m: res] =
            Pr[SConsis2(HeliosMix(Pe, Ve, ValidNothing, Pz, Vz), 
                       ValidNothing, AC2, HRO.RO, G).main() @ &m: res].
    by byequiv =>//=; sim.

  by rewrite (consis2 ValidNothing Pe Ve Pz Vz G S NoRelation A AC2 AC3 v_distinct 
            Verify_to_verify LPKE_prover_keepstate Prover_to_verify Prover_to_verify_left 
            validInd_ax Gi_ll Go_ll Pz_ll Vz_ll Si_ll So_ll Sp_ll A1_ll A2_ll AC2_ll AS_ll 
            Vval_ll Vvot_ll Pe_ll Ve_ll C_ll relConstraint enc_to_validInd &m).
qed.

equiv consis3 &m:
    SConsis3_L(BasicScheme(Pe, Ve, Pz, Vz), 
               ValidNothing, AC3, HRO.RO, G).main ~ 
    SConsis3_R(BasicScheme(Pe, Ve, Pz, Vz), 
               CE(IPKE(Pe,Ve)), ValidNothing, AC3, HRO.RO, G).main
    : ={glob HRO.RO, glob G, glob IPKE(Pe,Ve), 
        glob ValidNothing, glob Pz, glob AC3} ==> ={res}.
proof.

  transitivity SConsis3_L(HeliosMix(Pe, Ve, ValidNothing, Pz, Vz), 
                          ValidNothing, AC3, HRO.RO, G).main 
  (={glob HRO.RO, glob G, glob IPKE(Pe,Ve), glob ValidNothing, glob Pz, glob AC3} ==> 
   ={res})
  (={glob HRO.RO, glob G, glob IPKE(Pe,Ve), glob ValidNothing, glob Pz, glob AC3} ==> 
   ={res})=>//=. 

  + by progress; smt.
  + by proc; sim. 
  
  transitivity SConsis3_R(HeliosMix(Pe, Ve, ValidNothing, Pz, Vz), 
                          CE(IPKE(Pe,Ve)), ValidNothing, AC3, HRO.RO, G).main 
  (={glob HRO.RO, glob G, glob IPKE(Pe,Ve), glob ValidNothing, glob Pz, glob AC3} ==> 
   ={res})
  (={glob HRO.RO, glob G, glob IPKE(Pe,Ve), glob ValidNothing, glob Pz, glob AC3} ==> 
   ={res})=>//=. 

  + by progress; smt.

  + by rewrite (consis3 ValidNothing Pe Ve Pz Vz G S NoRelation A AC2 AC3 v_distinct 
            Verify_to_verify LPKE_prover_keepstate Prover_to_verify Prover_to_verify_left 
            validInd_ax Gi_ll Go_ll Pz_ll Vz_ll Si_ll So_ll Sp_ll A1_ll A2_ll AC2_ll AS_ll 
            Vval_ll Vvot_ll Pe_ll Ve_ll C_ll relConstraint enc_to_validInd &m). 
  by sim. 
qed.

(* STRONG CORRECTNESS *)
lemma scorr (AS <: SCorr_Adv' { IPKE(Pe,Ve), Pz, Vz, ValidNothing, HRO.RO, BSC, BS, G}) &m:
  Pr[SCorr(BasicScheme(Pe, Ve, Pz, Vz), 
           AS(BasicScheme(Pe, Ve, Pz, Vz)), HRO.RO, G).main() @ &m: BSC.valid] 
= 
`|Pr[Ind1CCA(IPKE(Pe,Ve), 
             INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, ValidNothing), 
                       AS(MV(IPKE(Pe,Ve), Pz, Vz, ValidNothing)), G, HRO.RO)), 
             HRO.RO,Left).main() @ &m: res /\  size BS.encL <= 1] -
  Pr[Ind1CCA(IPKE(Pe,Ve), 
             INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, ValidNothing), 
                       AS(MV(IPKE(Pe,Ve), Pz, Vz, ValidNothing)), G, HRO.RO)),
             HRO.RO,Right).main()  @ &m: res /\  size BS.encL <= 1]|.
proof.  
  have ->: Pr[SCorr(BasicScheme(Pe, Ve, Pz, Vz), 
                    AS(BasicScheme(Pe, Ve, Pz, Vz)), 
                    HRO.RO, G).main() @ &m: BSC.valid]=
           Pr[SCorr(HeliosMix(Pe, Ve, ValidNothing, Pz, Vz), 
                    AS(HeliosMix(Pe, Ve, ValidNothing, Pz, Vz)), 
                    HRO.RO, G).main() @ &m: BSC.valid].
    by byequiv =>//=; sim.

  by rewrite (scorr ValidNothing Pe Ve Pz Vz G S NoRelation A AC2 AC3 v_distinct 
            Verify_to_verify LPKE_prover_keepstate Prover_to_verify Prover_to_verify_left 
            validInd_ax Gi_ll Go_ll Pz_ll Vz_ll Si_ll So_ll Sp_ll A1_ll A2_ll AC2_ll AS_ll 
            Vval_ll Vvot_ll Pe_ll Ve_ll C_ll relConstraint enc_to_validInd AS &m).
qed.
