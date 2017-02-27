require import Option List.
require (*  *) PreHelios DiffieHellman.
require import Distr NewDistr Perms Int IntExtra FMap FSet Real Pair Mu_mem. 
require import LeftOrRight.

(* basic types and operators used for the encryption scheme space *)
  type skey, pkey, ident, label, pubBB, vote.
  type h_cipher, h_stm, h_prf, h_in, h_out, h_data.

  (* voting operators *)
  op Policy['a]: (ident * 'a) list  -> (ident * 'a) list.

  (* remove non-valid votes *)
  op removeInvalid  (ubb: (ident * vote option) list) =
    with ubb = "[]"         => []
    with ubb = (::) idv ubb => if idv.`2 = None
                              then removeInvalid ubb
                              else (idv.`1, oget idv.`2) :: removeInvalid ubb.

(* Rho operator: uniform distribution of the list for the last valid votes *)
op Rho (ubb:(ident * vote option) list)  : (vote list) distr
       = if (removeInvalid ubb = []) then MUnit.dunit []
         else MUniform.duniform (allperms (map snd (Policy (removeInvalid ubb)))).

clone export PreHelios as HM with
  type label      <- label,
  type MV2.ident  <- ident,
  type MV2.result <- vote list,
  type fq         <- vote,
  type skey       <- skey,
  type pkey       <- pkey,
  type h_stm      <- h_stm,
  type h_in       <- h_in,
  type h_out      <- h_out,
  type h_data     <- h_data,
  type h_cipher   <- h_cipher,
  type h_prf      <- h_prf,
  type MV2.pubBB  <- pubBB,
  op MV2.Rho      <- Rho. 


(* ---------------------------------------------------------------------- *)
module HeliosMix (Pe: PSpke.Prover, Ve: PSpke.Verifier, 
                      C: ValidInd, Pz: Prover,  Vz: Verifier,
                      H: HOracle.ARO,  G: GOracle.ARO) = 
   MV(IPKE(Pe,Ve), Pz, Vz, C, H, G). 

(* Security Properties: BPRIV, Strong Consistency, Strong Correctness *)
section Security.

declare module C: ValidInd        { BP, BS, BPS, BSC, BSCorr, BIND, HRO.RO,
                                    BPRIV_SB, BIND2, PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv}. 
declare module Pe: PSpke.Prover   {C, BS, BP, BSC, BSCorr, HRO.RO, SCorr_Oracle, BPS, BIND,
                                   PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv, BPRIV_SB, BIND2 }.
declare module Ve: PSpke.Verifier {C, BS, BP, BSC, BSCorr, Pe, HRO.RO, BPS, BIND,
                                   PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv, BPRIV_SB, BIND2}.

declare module Pz: Prover         {C, Pe, Ve, BP, BS, BSCorr, BIND, HRO.RO, BPS, BSC }.
declare module Vz: Verifier       {C, Pe, Ve, Pz, BP, BS, BSCorr, BIND, HRO.RO, BPS, BSC }.
declare module G : GOracle.Oracle {C, Pe, Ve, Pz, Vz, BP, HRO.RO, BSC, BPS, BS, BIND, SCorr_Oracle,
                                   BSCorr}.
declare module S : Simulator      {C, Pe, Ve, Pz, Vz, G, BS, BP, BSC, BSCorr, HRO.RO, BSC, BPS,
                                   BPRIV_SB, BIND2, BIND, PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv}.
declare module Rz: VotingRelation'{ BPS, BP, BS, G, S, Pz, Vz, C, Ve, Pe, HRO.RO}.

(* adversary models *)
declare module A : BPRIV_Adv      {C, Pe, Ve, Pz, Vz, Rz, G, S, HRO.RO, BP, BS, BSCorr, BSC, BPS,
                                   PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv, BPRIV_SB, BIND, BIND2 }.
declare module AC2: SConsis2_Adv {BP, HRO.RO, G, C}.
declare module AC3: SConsis3_Adv {BP, HRO.RO, Pe, Ve, Pz, C, G}.

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
 
  (* axiom linking C.validInd to validInd operator *)
  axiom validInd_ax (gc: (glob C)) (pk: pkey) (b: ident * label * cipher):
    phoare[C(HRO.RO).validInd: 
            (glob C) = gc /\ arg = (b, pk) 
            ==>
            (glob C) = gc /\ res = validInd pk b HRO.RO.m] = 1%r.

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

  (* -> validInd *)
  axiom C_ll (H <: HOracle.ARO):
    islossless H.o => 
    islossless C(H).validInd.

  (* axiom on a voting relation that does not 
     change the eager random oracle state *)
  axiom relConstraint (gh : (glob HRO.RO)):
    phoare[ Rz(IPKE(Pe,Ve),HRO.RO).main : 
          (glob HRO.RO) = gh ==> (glob HRO.RO) = gh] = 1%r.

  (* axiom on Policy keeping some valid elements *)
  axiom nonE_to_nonE (x: (ident * vote option) list):
    removeInvalid x <> [] =>
    map snd (Policy (removeInvalid x)) <> [].

  (* encryption implis validInd *)
  axiom enc_to_validInd (pkx: pkey) (id: ident) (v: plain) (l : label):
    equiv[IPKE(Pe,Ve,HRO.RO).enc ~ IPKE(Pe,Ve,HRO.RO).enc: 
         ={glob HRO.RO, glob IPKE(Pe,Ve), arg} /\ arg{1} = (pkx,l,v) 
         ==> ={res, glob IPKE(Pe,Ve), glob HRO.RO} /\
          validInd pkx (id, l, res{1}) HRO.RO.m{1}].
(* ** end *)

(* lemmas for distribution of permutations *)
local lemma sf (x: (ident * vote option) list):
  x <> [] =>
  weight (MUniform.duniform x) = 1%r. 
proof.
  move => Hx. by smt. 
qed.
 
local lemma sd (x: (ident * vote option) list):
  x = [] =>
  weight (MUnit.dunit x) = 1%r by smt.

local lemma sds (x:'a list) (z: 'a):
  mem x z = true => x <> [].
proof. 
  by elim: x =>//=.
qed.

local lemma ddg (x: vote list):
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

local lemma nosmt Rho_weight (x: (ident * vote option) list):
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
  have Hy: map snd (Policy (removeInvalid x)) <> [] by rewrite (nonE_to_nonE x Hx).
  by rewrite (ddg _ Hy).
qed.


(* bound on the scorr in bpriv by ind1cca *)
lemma scorr_bpriv (LR<: LorR { BS, BP, BIND, BIND2, BSCorr, BSC, 
                                     HRO.RO, A, Ve, C, Vz, Pz, Pe, S}) &m:
  Pr[SCorr (HeliosMix(Pe, Ve, C, Pz, Vz), 
            BSCorr(HeliosMix(Pe, Ve, C, Pz, Vz),A, LR), 
            HRO.RO, S).main() @ &m: BSC.valid]
  = 
`|Pr[Ind1CCA(IPKE(Pe,Ve),
             INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, C), 
                       BSCorr(MV(IPKE(Pe,Ve),Pz,Vz, C),A, LR), S, HRO.RO)),
             HRO.RO,Left).main() @ &m: res /\  size BS.encL <= 1] -
  Pr[Ind1CCA(IPKE(Pe,Ve),
             INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, C),
                       BSCorr(MV(IPKE(Pe,Ve),Pz,Vz, C),A, LR), S, HRO.RO)),
             HRO.RO,Right).main()  @ &m: res /\  size BS.encL <= 1]|. 
proof. 
  have ->: Pr[SCorr (HeliosMix(Pe, Ve, C, Pz, Vz), 
                     BSCorr(HeliosMix(Pe, Ve, C, Pz, Vz),A, LR), 
                     HRO.RO, S).main() @ &m: BSC.valid] =
           Pr[SCorr (MV(IPKE(Pe,Ve), Pz, Vz, C), 
                     BSCorr(MV(IPKE(Pe,Ve), Pz, Vz, C),A, LR), 
                     HRO.RO, S).main() @ &m: BSC.valid].
    by byequiv =>//=; sim.
  by rewrite (scorr_bpriv Pe Ve C S Vz Pz A Pe_ll Ve_ll AS_ll So_ll Si_ll v_distinct
                      Prover_to_verify Prover_to_verify_left Verify_to_verify 
                      enc_to_validInd validInd_ax LR &m).
qed.

(* lemma bounding bpriv *)
lemma bpriv &m: 
   `|Pr[BPRIV_L(HeliosMix(Pe, Ve, C, Pz, Vz), A, HRO.RO, G).main() @ &m : res] -
     Pr[BPRIV_R(HeliosMix(Pe, Ve, C, Pz, Vz), A, HRO.RO, G, S).main() @ &m :res]|
<=
     Pr[VFR(IPKE(Pe, Ve), BVFR(MV(IPKE(Pe, Ve), Pz, Vz, C), A), 
            Rz(IPKE(Pe,Ve)), HRO.RO, G).main() @ &m : res] +
     Pr[VFR(IPKE(Pe, Ve), BVFR(MV(IPKE(Pe, Ve), Pz, Vz, C), A), 
            Rz(IPKE(Pe,Ve)), HRO.RO, S).main() @ &m : res] +
   `|Pr[ZK_L(Rz(IPKE(Pe, Ve), HRO.RO), 
             Pz, BZK(IPKE(Pe, Ve), Pz, C, Vz, A, HRO.RO), G).main() @ &m : res] -
     Pr[ZK_R(Rz(IPKE(Pe, Ve), HRO.RO),
             S, BZK(IPKE(Pe, Ve), Pz, C, Vz, A, HRO.RO)).main() @ &m : res]| +
n%r *
    `|Pr[Ind1CCA(IPKE(Pe,Ve),
                 INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, C), 
                           BSCorr(MV(IPKE(Pe,Ve),Pz,Vz, C),A, Left), S, HRO.RO)),
                 HRO.RO,Left).main() @ &m: res /\  size BS.encL <= 1] -
      Pr[Ind1CCA(IPKE(Pe,Ve),
                 INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, C),
                           BSCorr(MV(IPKE(Pe,Ve),Pz,Vz, C),A, Left), S, HRO.RO)),
                 HRO.RO,Right).main() @ &m: res /\  size BS.encL <= 1]| +
n%r *
    `|Pr[Ind1CCA(IPKE(Pe,Ve),
                 INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, C), 
                           BSCorr(MV(IPKE(Pe,Ve),Pz,Vz, C),A, Right), S, HRO.RO)),
                 HRO.RO,Left).main() @ &m: res /\  size BS.encL <= 1] -
      Pr[Ind1CCA(IPKE(Pe,Ve),
                 INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, C),
                           BSCorr(MV(IPKE(Pe,Ve),Pz,Vz, C),A, Right), S, HRO.RO)),
                 HRO.RO,Right).main() @ &m: res /\  size BS.encL <= 1]| +
n%r *
   `|Pr[Ind1CCA(IPKE(Pe, Ve), 
                WrapAdv(BIND(MV(IPKE(Pe, Ve), Pz, Vz, C), A, S), 
                        IPKE(Pe, Ve), HRO.RO),
                HRO.RO, Left).main() @ &m : res /\ WrapAdv.l <= n /\ size BS.encL <= 1] -
     Pr[Ind1CCA(IPKE(Pe, Ve), 
                WrapAdv(BIND(MV(IPKE(Pe, Ve), Pz, Vz, C), A, S), 
                        IPKE(Pe, Ve), HRO.RO), 
                HRO.RO, Right).main()@ &m : res /\ WrapAdv.l <= n /\ size BS.encL <= 1]|.
proof.
  have ->: Pr[BPRIV_L(HeliosMix(Pe, Ve, C, Pz, Vz), 
                      A, HRO.RO, G).main() @ &m : res] =
           Pr[BPRIV_L(MV(IPKE(Pe, Ve), Pz, Vz, C), 
                      A, HRO.RO, G).main() @ &m : res].
    by byequiv =>//=; sim.
  have ->: Pr[BPRIV_R(HeliosMix(Pe, Ve, C, Pz, Vz), 
                      A, HRO.RO, G, S).main() @ &m : res] =
           Pr[BPRIV_R(MV(IPKE(Pe, Ve), Pz, Vz, C), 
                      A, HRO.RO, G, S).main() @ &m : res].
    by byequiv =>//=; sim.
    
  cut := bpriv G S Vz Pz Rz C A Ve Pe Verify_to_verify 
                   LPKE_prover_keepstate Prover_to_verify Prover_to_verify_left 
                   validInd_ax relConstraint Rho_weight Gi_ll 
                   Go_ll Pz_ll Vz_ll Si_ll So_ll Sp_ll A1_ll A2_ll C_ll Vval_ll Vvot_ll 
                   Pe_ll Ve_ll &m.

  (* make the scorr equal to ind1cca *)
  have ->: Pr[SCorr(MV(IPKE(Pe, Ve), Pz, Vz, C), 
              BSCorr(MV(IPKE(Pe, Ve), Pz, Vz, C), A, Left), 
              HRO.RO, S).main() @ &m : BSC.valid] = 
           Pr[SCorr (HeliosMix(Pe, Ve, C, Pz, Vz), 
              BSCorr(HeliosMix(Pe, Ve, C, Pz, Vz),A, Left), 
              HRO.RO, S).main() @ &m: BSC.valid].
    by byequiv =>//=; sim.
  rewrite (scorr_bpriv Left &m).
  have ->: Pr[SCorr(MV(IPKE(Pe, Ve), Pz, Vz, C), 
              BSCorr(MV(IPKE(Pe, Ve), Pz, Vz, C), A, Right), 
              HRO.RO, S).main() @ &m : BSC.valid] = 
           Pr[SCorr (HeliosMix(Pe, Ve, C, Pz, Vz), 
              BSCorr(HeliosMix(Pe, Ve, C, Pz, Vz),A, Right), 
              HRO.RO, S).main() @ &m: BSC.valid].
    by byequiv =>//=; sim.
  by rewrite (scorr_bpriv Right &m). 
qed.


(* STRONG CONSITENCY *) 
lemma consis1(id: ident, v: plain, l: label) &m: 
   Pr[SConsis1(HeliosMix(Pe, Ve, C, Pz, Vz), 
               CE(IPKE(Pe,Ve)), HRO.RO, G).main(id,v, l) @ &m: res]  >=
   Pr[PKEvf.Correctness(IPKE(Pe,Ve), HRO.RO).main(v,l) @ &m: res].
proof.
  have ->: Pr[SConsis1(HeliosMix(Pe, Ve, C, Pz, Vz), 
                       CE(IPKE(Pe,Ve)), HRO.RO, G).main(id,v, l) @ &m: res] =
           Pr[SConsis1(MV(IPKE(Pe, Ve), Pz, Vz, C), 
                       CE(IPKE(Pe,Ve)), HRO.RO, G).main(id,v, l) @ &m: res].
    by byequiv =>//=; sim.

  by rewrite (consis1 HRO.RO G S Vz Pz Ve Pe C AC2 AC3
                      Gi_ll Go_ll C_ll Pz_ll AC2_ll Rho_weight validInd_ax id v l &m).
qed.

lemma consis2 &m:
  Pr[SConsis2(HeliosMix(Pe, Ve, C, Pz, Vz), 
              C, AC2, HRO.RO, G).main() @ &m: res] = 1%r.
proof. 
  have ->: Pr[SConsis2(HeliosMix(Pe, Ve, C, Pz, Vz), 
                       C, AC2, HRO.RO, G).main() @ &m: res] =
           Pr[SConsis2(MV(IPKE(Pe, Ve), Pz, Vz, C), 
                       C, AC2, HRO.RO, G).main() @ &m: res].
    by byequiv =>//=; sim.

  by rewrite (consis2 HRO.RO G S Vz Pz Ve Pe C AC2 AC3
                      Gi_ll Go_ll C_ll Pz_ll AC2_ll Rho_weight validInd_ax &m).
qed.

equiv consis3 &m:
    SConsis3_L(HeliosMix(Pe, Ve, C, Pz, Vz), 
               C, AC3, HRO.RO, G).main ~ 
    SConsis3_R(HeliosMix(Pe, Ve, C, Pz, Vz), 
               CE(IPKE(Pe,Ve)), C, AC3, HRO.RO, G).main
    : ={glob HRO.RO, glob G, glob IPKE(Pe,Ve), 
        glob C, glob Pz, glob AC3} ==> ={res}.
proof.

  transitivity SConsis3_L(MV(IPKE(Pe, Ve), Pz, Vz, C), 
                          C, AC3, HRO.RO, G).main 
  (={glob HRO.RO, glob G, glob IPKE(Pe,Ve), glob C, glob Pz, glob AC3} ==> 
   ={res})
  (={glob HRO.RO, glob G, glob IPKE(Pe,Ve), glob C, glob Pz, glob AC3} ==> 
   ={res})=>//=. 

  + by progress; smt.
  + proc; sim. 
  
  transitivity SConsis3_R(MV(IPKE(Pe, Ve), Pz, Vz, C), 
                          CE(IPKE(Pe,Ve)), C, AC3, HRO.RO, G).main 
  (={glob HRO.RO, glob G, glob IPKE(Pe,Ve), glob C, glob Pz, glob AC3} ==> 
   ={res})
  (={glob HRO.RO, glob G, glob IPKE(Pe,Ve), glob C, glob Pz, glob AC3} ==> 
   ={res})=>//=. 

  + by progress; smt.

  + conseq (_: ={glob HRO.RO, glob G, glob IPKE(Pe, Ve), 
                 glob C, glob AC3} ==> _); first by progress. 

    by rewrite (consis3 HRO.RO G S Vz Pz Ve Pe C AC2 AC3
                      Gi_ll Go_ll C_ll Pz_ll AC2_ll Rho_weight validInd_ax &m).
  by sim. 
qed.

(* STRONG CORRECTNESS *)
lemma scorr (AS <: SCorr_Adv' { IPKE(Pe,Ve), Pz, Vz, C, HRO.RO, BSC, BS, G}) &m:
  Pr[SCorr(HeliosMix(Pe, Ve, C, Pz, Vz), 
              AS(HeliosMix(Pe, Ve, C, Pz, Vz)), HRO.RO, G).main() @ &m: BSC.valid] = 
`|Pr[Ind1CCA(IPKE(Pe,Ve), 
             INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, C), 
                       AS(MV(IPKE(Pe,Ve), Pz, Vz, C)), G, HRO.RO)), 
             HRO.RO,Left).main() @ &m: res /\  size BS.encL <= 1] -
  Pr[Ind1CCA(IPKE(Pe,Ve), 
             INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, C), 
                       AS(MV(IPKE(Pe,Ve), Pz, Vz, C)), G, HRO.RO)),
             HRO.RO,Right).main()  @ &m: res /\  size BS.encL <= 1]|.
proof.  
  have ->: Pr[SCorr(HeliosMix(Pe, Ve, C, Pz, Vz), 
                    AS(HeliosMix(Pe, Ve, C, Pz, Vz)), 
                    HRO.RO, G).main() @ &m: BSC.valid] =
           Pr[SCorr(MV(IPKE(Pe,Ve), Pz, Vz, C), 
                    AS(MV(IPKE(Pe,Ve),Pz,Vz, C)), 
                    HRO.RO, G).main() @ &m: BSC.valid].
    by byequiv =>//=; sim.

  by rewrite (scorr Pe Ve C S Vz Pz A Pe_ll Ve_ll AS_ll So_ll Si_ll v_distinct
                      Prover_to_verify Prover_to_verify_left Verify_to_verify 
                      enc_to_validInd validInd_ax AS G &m Gi_ll Go_ll).
qed.

lemma bound_vfr (Gx <: GOracle.Oracle{BS, BP, HRO.RO, A, Ve, Pe, C}) &m:
  islossless Gx.init =>
  islossless Gx.o => 
  Pr[VFR(IPKE(Pe, Ve),BVFR(MV(IPKE(Pe, Ve),Pz, Vz,C), A), 
         DecRelation(IPKE(Pe, Ve)), HRO.RO, Gx).main() @ &m : res] = 0%r.
proof.

  by exact (bound_vfr G S Vz Pz C A  Ve Pe A1_ll So_ll Si_ll Go_ll Gi_ll 
                      C_ll Pe_ll Ve_ll Verify_to_verify  Rho_weight Gx &m).
qed.

lemma bound2_vfr (Gx <: GOracle.Oracle{BS, BP, HRO.RO, A, Ve, Pe, C}) &m:
  islossless Gx.init =>
  islossless Gx.o => 
  Pr[VFR(IPKE(Pe, Ve),BVFR(MV(IPKE(Pe, Ve),Pz, Vz,C), A), 
         NoRelation(IPKE(Pe, Ve)), HRO.RO, Gx).main() @ &m : res] = 0%r.
proof.
  by exact (bound2_vfr G S Vz Pz C A  Ve Pe A1_ll So_ll Si_ll Go_ll Gi_ll 
                      C_ll Pe_ll Ve_ll Verify_to_verify  Rho_weight Gx &m).
qed.
end section Security.