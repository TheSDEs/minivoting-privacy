require import Option List.
require (*  *) Helios_mix_perm DiffieHellman.
require import Distr NewDistr Perms Int IntExtra FMap FSet Real Pair Mu_mem. 
require import LeftOrRight.

(* ###############################################################
   Helios version 3 with mixnets and true identities,
   obtain from HeliosAbstract with 
   -1. the label (Flabel)   = empty
   -2. Publish              = last ballot for each voter
   -3. tally operator (Rho) = multiset over the last vote of a voter
   -4. ValidInd             = check proof
   -5. relation (R)         = correct decryption
   ###############################################################
   
*)

(* the space for the secret key and public key *)
  clone export CyclicGroup as Ksp.
  type skey = t.
  type pkey = group.

(*  ---------------------------------------------------------------------- *)
  (* voter identity: name + uuid + voter_id + voter_type *)
  type alias_name, uuid.
  type ident = alias_name * uuid.

(* ---------------------------------------------------------------------- *)
(* 1. Flabel: empty *)
  type label = unit. 
  const lblx: label.
  op Flabel(id: ident)= lblx.

(* ---------------------------------------------------------------------- *)
(* 2. Publish: full view on the last ballot for any id  *)

  type  h_cipher, h_stm, h_prf, h_in, h_out, h_data.

  (* check if there exists a ballot in bb, that containst this identity id *)
  op exists_id (id: ident, bb: (ident * label * (h_cipher * h_prf* h_data)) list) =
    with bb = [] => false
    with bb = b:: bb' => (id = b.`1) \/ (exists_id id bb').

  (* keep the last ballot for any id *)
  op keep_last(bb: (ident * label * (h_cipher * h_prf* h_data)) list)=
    with bb = "[]"      => []
    with bb = (::) b bb' => if (exists_id b.`1 bb')
                         then keep_last bb'
                         else b :: keep_last bb'.
  (* last ballot for each voter *)
  type pubBB= (alias_name * label * (h_cipher * h_prf* h_data)) list.
  op Publish(bb: (ident * label * (h_cipher * h_prf* h_data)) list): pubBB = 
    map (fun (b: (ident * label * (h_cipher * h_prf* h_data))) => (b.`1.`1, b.`2, b.`3) ) 
    (keep_last bb).

(* ---------------------------------------------------------------------- *)
(* 3. Rho: multiset( last vote policy)   *)
  (* last vote policy *)
  op Policy['a] (bb : (ident * 'a) list) =
    with bb = "[]"      => []
    with bb = (::) b bb => if   has (Fun.(\o) (pred1 b.`1) fst) bb
                           then Policy bb
                           else b :: Policy bb.
  (* Rho defined in Helios-mix-ord *) 

(* ---------------------------------------------------------------------- *)
(* 4. ValidInd - part 1 operator: check the proof using the operator verify *)
   (* op that creates a statement for the proof system used in encryption *)
    op to_statement: pkey -> label -> h_cipher -> h_stm.
    (* op that checks if proof for the statement used in encryption *)
    op verify : h_stm -> h_prf -> (h_in, h_out) map -> bool.

  op validInd (pk: pkey, b: (ident * label * (h_cipher* h_prf* h_data)), ro: (h_in, h_out) map) =
     verify (to_statement pk b.`2 b.`3.`1) b.`3.`2 ro.

clone export Helios_mix_perm as Hv3M with
  type label    <- label,
  type ident    <- ident,
  type skey     <- skey,
  type pkey     <- pkey,
  type h_stm    <- h_stm,
  type h_in     <- h_in,
  type h_out    <- h_out,
  type h_data   <- h_data,
  type h_cipher <- h_cipher,
  type h_prf    <- h_prf,
  type pubBB    <- pubBB,
  op HM.verify       <- verify,
  op HM.to_statement <- to_statement,
  op HM.MV2.Publish  <- Publish,
  op HM.MV2.Flabel   <- Flabel,
  op HM.MV2.validInd <- validInd,
  op Policy['a]      <- Policy. 

(* ---------------------------------------------------------------------- *)
(* 4. ValidInd - part 2 function: check the proof using the random oracle access *) 

module ValidProof(Ve:PSpke.Verifier, H: Ipke.ARO) = {
  proc validInd( b: (ident * label * cipher), pk: pkey): bool ={
    var ev;
    ev <@ Ve(H).verify(to_statement pk b.`2 b.`3.`1, b.`3.`2);
    return ev;
  }
}.

(* ---------------------------------------------------------------------- *)
(* 5. Relation (R): correct decryption  *)
  module DecRel(Pe: PSpke.Prover, Ve: PSpke.Verifier, 
                E: Scheme, H: HOracle.ARO) = DecRelation(E, H).

(* ---------------------------------------------------------------------- *)
(* Helios Version 3 with mix-nets and true identities *) 
module Heliosv3Mix (Pe: PSpke.Prover, Ve: PSpke.Verifier, 
                    Ve2: PSpke.Verifier,
                    Pz: Prover,  Vz: Verifier,
                    H: HOracle.ARO,   G: GOracle.ARO) 
    =  HeliosMix(Pe,Ve, ValidProof(Ve2), Pz, Vz, H, G).

(* Security Properties: BPRIV, Strong Consistency, Strong Correctness *)
section Security.

declare module Cv: PSpke.Verifier { BP, BS, BPS, BSC, BSCorr, BIND, HRO.RO,
                                    BPRIV_SB, BIND2, PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv}. 
declare module Pe: PSpke.Prover   {Cv, BS, BP, BSC, BSCorr, HRO.RO, SCorr_Oracle, BPS, BIND,
                                   PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv, BPRIV_SB, BIND2 }.
declare module Ve: PSpke.Verifier {Cv, BS, BP, BSC, BSCorr, Pe, HRO.RO, BPS, BIND,
                                   PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv, BPRIV_SB, BIND2}.

declare module Pz: Prover         {Cv, Pe, Ve, BP, BS, BSCorr, BIND, HRO.RO, BPS, BSC }.
declare module Vz: Verifier       {Cv, Pe, Ve, Pz, BP, BS, BSCorr, BIND, HRO.RO, BPS, BSC }.
declare module G : GOracle.Oracle {Cv, Pe, Ve, Pz, Vz, BP, HRO.RO, BSC, BPS, BS, BIND, SCorr_Oracle,
                                   BSCorr}.
declare module S : Simulator      {Cv, Pe, Ve, Pz, Vz, G, BS, BP, BSC, BSCorr, HRO.RO, BSC, BPS,
                                   BPRIV_SB, BIND2, BIND, PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv}.

(* adversary models *)
declare module A : BPRIV_Adv      {Cv, Pe, Ve, Pz, Vz, G, S, HRO.RO, BP, BS, BSCorr, BSC, BPS,
                                   PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv, BPRIV_SB, BIND, BIND2 }.
declare module AC2: SConsis2_Adv {BP, HRO.RO, G, Cv}.
declare module AC3: SConsis3_Adv {BP, HRO.RO, Pe, Ve, Pz, Cv, G}.

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

  (* axiom linking Ve.verify to verify operator *)
  axiom Verify_to_verify' (gc: (glob Cv)) (s: h_stm) (p: h_prf):
    phoare[Cv(HRO.RO).verify: (glob Cv) = gc /\ arg = (s, p)
         ==>
         (glob Cv) = gc /\
         res = verify s p HRO.RO.m] = 1%r.

  (* axiom on state of prover *)
  axiom LPKE_prover_keepstate (gp: (glob Pe)) (H<: HOracle.ARO):
    phoare[Pe(H).prove: 
          (glob Pe) = gp ==> (glob Pe) = gp] = 1%r.

  (* axiom transforming a proof in a verification (two-sided) *)
  axiom Prover_to_verify (s: h_stm) (w: h_wit):
    equiv[ Pe(HRO.RO).prove ~ Pe(HRO.RO).prove: 
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
  axiom Gi_ll: islossless G.init. 
  axiom Go_ll: islossless G.o.

  axiom Pz_ll (G <: GOracle.ARO):
    islossless G.o => 
    islossless Pz(G).prove.
  axiom Vz_ll (G <: GOracle.ARO):
    islossless G.o => 
    islossless Vz(G).verify.

  axiom Si_ll: islossless S.init.
  axiom So_ll: islossless S.o.
  axiom Sp_ll: islossless S.prove.

  (* adversary calls *)
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

  axiom Vval_ll (V<: VotingScheme) (H<: HOracle.ARO) (G<:GOracle.ARO) :
   islossless H.o =>
   islossless G.o =>
   islossless V(H,G).valid.  

  axiom Vvot_ll (V<: VotingScheme) (H<: HOracle.ARO) (G<:GOracle.ARO) :
   islossless H.o =>
   islossless G.o =>
   islossless V(H,G).vote. 

  axiom Pe_ll (H <: HOracle.ARO):
    islossless H.o => 
    islossless Pe(H).prove.
  axiom Ve_ll (H <: HOracle.ARO):
    islossless H.o => 
    islossless Ve(H).verify.

  axiom Cv_ll (H <: HOracle.ARO):
    islossless H.o => 
    islossless Cv(H).verify.
(* ** end *)

local lemma C_ll (H <: HOracle.ARO):
  islossless H.o => 
  islossless ValidProof(Cv, H).validInd.
proof.
  move => Ho; proc.   
  by call (Cv_ll H Ho). 
qed.   

(* linking C.validInd to validInd operator *)
lemma validInd_ax (gc: (glob ValidProof(Cv))) (pk: pkey) (b: ident * label * cipher):
  phoare[ValidProof(Cv, HRO.RO).validInd: 
         (glob ValidProof(Cv)) = gc /\ arg = (b, pk) 
          ==>
          (glob ValidProof(Cv)) = gc /\ res = validInd pk b HRO.RO.m] = 1%r.
proof.
  by proc; call (Verify_to_verify' gc (to_statement pk b.`2 b.`3.`1) b.`3.`2).
qed.

local lemma relCons (gh : (glob HRO.RO)):
    phoare[DecRel(Pe, Ve, IPKE(Pe, Ve), HRO.RO).main :
             (glob HRO.RO) = gh ==> (glob HRO.RO) = gh] = 1%r.
proof.
  proc.
  inline*.
  wp; while (HRO.RO.m = gh) (size wit.`2 -i); progress.
    wp; call (Ve_ll HRO.RO HRO.RO_o_ll).
    auto; progress.
    rewrite ltz_add2l //=. 
    rewrite -(ltz_add2l (i{hr}+1)) //=.   
    by rewrite addzAC //=. 
  auto; progress. 
  rewrite -lezNgt.
  by rewrite -(lez_add2r (-i0)).
qed. 

(* axiom on Policy keeping some valid elements *)
local lemma nonE_to_nonE (x: (ident * vote option) list):
    removeInvalid x <> [] =>
    map snd (Policy (removeInvalid x)) <> [].
proof.
  have Hy: forall (y: (ident * vote) list), 
           y <>[] => map snd y <> [] by smt.
  have Hz: forall (z: (ident * vote) list),
           z <>[] => Policy z <> [].
    by elim =>//=; smt.
  move => Hr.
  by rewrite (Hy (Policy (removeInvalid x)) (Hz (removeInvalid x) Hr)). 
qed.

local lemma enc_to_validInd (pkx: pkey) (id: ident) (v: plain) (l : label):
  equiv[ IPKE(Pe,Ve,HRO.RO).enc ~ IPKE(Pe,Ve,HRO.RO).enc: 
         ={glob HRO.RO, glob IPKE(Pe,Ve), arg} /\ arg{1} = (pkx,l,v) 
         ==> ={res, glob IPKE(Pe,Ve), glob HRO.RO} /\
          validInd pkx (id, l, res{1}) HRO.RO.m{1}].
proof.
  proc.   
  seq 2 2: (={r, c, p, lbl, pk, glob Pe, glob Ve, glob HRO.RO}/\
            p{1} = v /\l = lbl{1}/\ pkx = pk{2})=>//=;
      first by auto.
  exists* lbl{1}, c{1}, p{1}, r{1}; elim* => lbl c p r.
  call (Prover_to_verify (to_statement pkx lbl c) (to_witness p r)).
  by auto; progress; smt.
qed.


(* BPRIV *)
(* bound on the scorr in bpriv by ind1cca *)
lemma scorr_bpriv_bound (LR<: LorR { BS, BP, BIND, BIND2, BSCorr, BSC, 
                                     HRO.RO, A, Ve, Cv, Vz, Pz, Pe, S}) &m:
  Pr[SCorr (Heliosv3Mix(Pe, Ve, Cv, Pz, Vz), 
            BSCorr(Heliosv3Mix(Pe, Ve, Cv, Pz, Vz),A, LR), 
            HRO.RO, S).main() @ &m: BSC.valid] = 
`|Pr[Ind1CCA(IPKE(Pe,Ve),
             INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, ValidProof(Cv)), 
                       BSCorr(MV(IPKE(Pe,Ve),Pz,Vz, ValidProof(Cv)),A, LR), S, HRO.RO)),
         HRO.RO,Left).main() @ &m: res /\  size BS.encL <= 1] -
  Pr[Ind1CCA(IPKE(Pe,Ve),
             INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, ValidProof(Cv)),
                       BSCorr(MV(IPKE(Pe,Ve),Pz,Vz, ValidProof(Cv)),A, LR), S, HRO.RO)),
         HRO.RO,Right).main() @ &m: res /\  size BS.encL <= 1]|. 
proof. 
  have ->: Pr[SCorr (Heliosv3Mix(Pe, Ve, Cv, Pz, Vz), 
                     BSCorr(Heliosv3Mix(Pe, Ve, Cv, Pz, Vz),A, LR), 
                     HRO.RO, S).main() @ &m: BSC.valid] =
           Pr[SCorr (HeliosMix(Pe,Ve, ValidProof(Cv), Pz, Vz), 
                     BSCorr(HeliosMix(Pe,Ve, ValidProof(Cv), Pz, Vz),A, LR), 
                     HRO.RO, S).main() @ &m: BSC.valid].
    by byequiv =>//=; sim. print scorr_bpriv.
  by rewrite (scorr_bpriv (ValidProof(Cv)) Pe Ve Pz Vz G S (<:DecRel(Pe,Ve)) A AC2 AC3 v_distinct
                      Verify_to_verify LPKE_prover_keepstate Prover_to_verify Prover_to_verify_left 
                      validInd_ax Gi_ll Go_ll Pz_ll Vz_ll Si_ll So_ll Sp_ll A1_ll A2_ll AC2_ll AS_ll
                      Vval_ll Vvot_ll Pe_ll Ve_ll C_ll relCons nonE_to_nonE enc_to_validInd LR &m).
qed.


(* vfr is 0 for this relation *)
lemma bound_vfr (Gx <: GOracle.Oracle{BS, BP, HRO.RO, A, Ve, Pe, Cv}) &m:
  islossless Gx.init =>
  islossless Gx.o => 
  Pr[VFR(IPKE(Pe, Ve),BVFR(MV(IPKE(Pe, Ve),Pz, Vz,ValidProof(Cv)), A), 
         DecRel(Pe,Ve,IPKE(Pe, Ve)), HRO.RO, Gx).main() @ &m : res] = 0%r.
proof.
   have ->: Pr[VFR(IPKE(Pe, Ve), 
                  BVFR(MV(IPKE(Pe, Ve), Pz, Vz, ValidProof(Cv)), A), 
                  DecRel(Pe,Ve,IPKE(Pe, Ve)), HRO.RO, Gx).main () @ &m : res] =
           Pr[VFR(IPKE(Pe, Ve), 
                  BVFR(MV(IPKE(Pe, Ve), Pz, Vz, ValidProof(Cv)), A), 
                  DecRelation(IPKE(Pe, Ve)), HRO.RO, Gx).main() @ &m : res].
    by byequiv =>//=; sim. 
  by exact (bound_vfr (ValidProof(Cv)) Pe Ve Pz Vz G S (<:DecRel(Pe,Ve)) A AC2 AC3 v_distinct
                      Verify_to_verify LPKE_prover_keepstate Prover_to_verify Prover_to_verify_left 
                      validInd_ax Gi_ll Go_ll Pz_ll Vz_ll Si_ll So_ll Sp_ll A1_ll A2_ll AC2_ll AS_ll
                      Vval_ll Vvot_ll Pe_ll Ve_ll C_ll relCons nonE_to_nonE enc_to_validInd Gx &m). 
qed.

(* Lemma bounding bpriv *)
lemma bpriv &m: 
   `|Pr[BPRIV_L(Heliosv3Mix(Pe, Ve, Cv, Pz, Vz), A, HRO.RO, G).main() @ &m : res] -
     Pr[BPRIV_R(Heliosv3Mix(Pe, Ve, Cv, Pz, Vz), A, HRO.RO, G, S).main() @ &m :res]|
<=
   `|Pr[ZK_L(DecRelation(IPKE(Pe, Ve), HRO.RO), 
             Pz, BZK(IPKE(Pe, Ve), Pz, ValidProof(Cv), Vz, A, HRO.RO), G).main() @ &m : res] -
     Pr[ZK_R(DecRelation(IPKE(Pe, Ve), HRO.RO),
             S, BZK(IPKE(Pe, Ve), Pz, ValidProof(Cv), Vz, A, HRO.RO)).main() @ &m : res]| +
n%r *
    `|Pr[Ind1CCA(IPKE(Pe,Ve),
                 INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, ValidProof(Cv)), 
                           BSCorr(MV(IPKE(Pe,Ve),Pz,Vz, ValidProof(Cv)),A, Left), S, HRO.RO)),
                 HRO.RO,Left).main() @ &m: res /\  size BS.encL <= 1] -
      Pr[Ind1CCA(IPKE(Pe,Ve),
                 INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, ValidProof(Cv)),
                           BSCorr(MV(IPKE(Pe,Ve),Pz,Vz, ValidProof(Cv)),A, Left), S, HRO.RO)),
                 HRO.RO,Right).main() @ &m: res /\  size BS.encL <= 1]| +
n%r *
    `|Pr[Ind1CCA(IPKE(Pe,Ve),
                 INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, ValidProof(Cv)), 
                           BSCorr(MV(IPKE(Pe,Ve),Pz,Vz, ValidProof(Cv)),A, Right), S, HRO.RO)),
                 HRO.RO,Left).main() @ &m: res /\  size BS.encL <= 1] -
      Pr[Ind1CCA(IPKE(Pe,Ve),
                 INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, ValidProof(Cv)),
                           BSCorr(MV(IPKE(Pe,Ve),Pz,Vz, ValidProof(Cv)),A, Right), S, HRO.RO)),
                 HRO.RO,Right).main() @ &m: res /\  size BS.encL <= 1]| +
n%r *
   `|Pr[Ind1CCA(IPKE(Pe, Ve), 
                WrapAdv(BIND(MV(IPKE(Pe, Ve), Pz, Vz, ValidProof(Cv)), A, S), 
                        IPKE(Pe, Ve), HRO.RO),
                HRO.RO, Left).main() @ &m : res /\ WrapAdv.l <= n /\ size BS.encL <= 1] -
     Pr[Ind1CCA(IPKE(Pe, Ve), 
                WrapAdv(BIND(MV(IPKE(Pe, Ve), Pz, Vz, ValidProof(Cv)), A, S), 
                        IPKE(Pe, Ve), HRO.RO), 
                HRO.RO, Right).main()@ &m : res /\ WrapAdv.l <= n /\ size BS.encL <= 1]|.
proof.
  have ->: Pr[BPRIV_L(Heliosv3Mix(Pe, Ve, Cv, Pz, Vz), 
                      A, HRO.RO, G).main() @ &m : res] =
           Pr[BPRIV_L(HeliosMix(Pe,Ve, ValidProof(Cv), Pz, Vz), 
                      A, HRO.RO, G).main() @ &m : res].
    by byequiv =>//=; sim.
  have ->: Pr[BPRIV_R(Heliosv3Mix(Pe, Ve, Cv, Pz, Vz), 
                      A, HRO.RO, G, S).main() @ &m : res] =
           Pr[BPRIV_R(HeliosMix(Pe,Ve, ValidProof(Cv), Pz, Vz), 
                      A, HRO.RO, G, S).main() @ &m : res].
    by byequiv =>//=; sim.
    
  cut := bpriv (ValidProof(Cv)) Pe Ve Pz Vz G S (<:DecRel(Pe,Ve)) A AC2 AC3 v_distinct
                      Verify_to_verify LPKE_prover_keepstate Prover_to_verify Prover_to_verify_left 
                      validInd_ax Gi_ll Go_ll Pz_ll Vz_ll Si_ll So_ll Sp_ll A1_ll A2_ll AC2_ll AS_ll
                      Vval_ll Vvot_ll Pe_ll Ve_ll C_ll relCons nonE_to_nonE enc_to_validInd &m.

  (* make the VFR experiment 0 *)
  by rewrite (bound_vfr G &m Gi_ll Go_ll) (bound_vfr S &m Si_ll So_ll).
qed.


(* Lemma bounding STRONG CONSITENCY *) 
lemma consis1(id: ident, v: plain, l: label) &m: 
   Pr[SConsis1(Heliosv3Mix(Pe, Ve, Cv, Pz, Vz), 
               CE(IPKE(Pe,Ve)), HRO.RO, G).main(id,v, l) @ &m: res]  >=
   Pr[PKEvf.Correctness(IPKE(Pe,Ve), HRO.RO).main(v,l) @ &m: res].
proof.
  have ->: Pr[SConsis1(Heliosv3Mix(Pe, Ve, Cv, Pz, Vz), 
                       CE(IPKE(Pe,Ve)), HRO.RO, G).main(id,v, l) @ &m: res] =
           Pr[SConsis1(HeliosMix(Pe,Ve, ValidProof(Cv), Pz, Vz), 
                       CE(IPKE(Pe,Ve)), HRO.RO, G).main(id,v, l) @ &m: res].
    by byequiv =>//=; sim.

  by rewrite (consis1 (ValidProof(Cv)) Pe Ve Pz Vz G S (<:DecRel(Pe,Ve)) A AC2 AC3 v_distinct
                 Verify_to_verify LPKE_prover_keepstate Prover_to_verify Prover_to_verify_left 
                 validInd_ax Gi_ll Go_ll Pz_ll Vz_ll Si_ll So_ll Sp_ll A1_ll A2_ll AC2_ll AS_ll
                 Vval_ll Vvot_ll Pe_ll Ve_ll C_ll relCons nonE_to_nonE enc_to_validInd id v l &m).
qed.

lemma consis2 &m:
  Pr[SConsis2(Heliosv3Mix(Pe, Ve, Cv, Pz, Vz), 
              ValidProof(Cv), AC2, HRO.RO, G).main() @ &m: res] = 1%r.
proof. 
  have ->: Pr[SConsis2(Heliosv3Mix(Pe, Ve, Cv, Pz, Vz), 
                       ValidProof(Cv), AC2, HRO.RO, G).main() @ &m: res] =
           Pr[SConsis2(HeliosMix(Pe,Ve, ValidProof(Cv), Pz, Vz), 
                       ValidProof(Cv), AC2, HRO.RO, G).main() @ &m: res].
    by byequiv =>//=; sim.

  by rewrite (consis2 (ValidProof(Cv)) Pe Ve Pz Vz G S (<:DecRel(Pe,Ve)) A AC2 AC3 v_distinct
                 Verify_to_verify LPKE_prover_keepstate Prover_to_verify Prover_to_verify_left 
                 validInd_ax Gi_ll Go_ll Pz_ll Vz_ll Si_ll So_ll Sp_ll A1_ll A2_ll AC2_ll AS_ll
                 Vval_ll Vvot_ll Pe_ll Ve_ll C_ll relCons nonE_to_nonE enc_to_validInd &m).
qed.

equiv consis3 &m:
    SConsis3_L(Heliosv3Mix(Pe, Ve, Cv, Pz, Vz), 
               ValidProof(Cv), AC3, HRO.RO, G).main ~ 
    SConsis3_R(Heliosv3Mix(Pe, Ve, Cv, Pz, Vz), 
               CE(IPKE(Pe,Ve)), ValidProof(Cv), AC3, HRO.RO, G).main
    : ={glob HRO.RO, glob G, glob IPKE(Pe,Ve), 
        glob ValidProof(Cv), glob Pz, glob AC3} ==> ={res}.
proof.

  transitivity SConsis3_L(HeliosMix(Pe,Ve, ValidProof(Cv), Pz, Vz), 
                          ValidProof(Cv), AC3, HRO.RO, G).main 
  (={glob HRO.RO, glob G, glob IPKE(Pe,Ve), glob ValidProof(Cv), glob Pz, glob AC3} ==> 
   ={res})
  (={glob HRO.RO, glob G, glob IPKE(Pe,Ve), glob ValidProof(Cv), glob Pz, glob AC3} ==> 
   ={res})=>//=. 

  + by progress; smt.
  + proc; sim. 
  
  transitivity SConsis3_R(HeliosMix(Pe,Ve, ValidProof(Cv), Pz, Vz), 
                          CE(IPKE(Pe,Ve)), ValidProof(Cv), AC3, HRO.RO, G).main 
  (={glob HRO.RO, glob G, glob IPKE(Pe,Ve), glob ValidProof(Cv), glob Pz, glob AC3} ==> 
   ={res})
  (={glob HRO.RO, glob G, glob IPKE(Pe,Ve), glob ValidProof(Cv), glob Pz, glob AC3} ==> 
   ={res})=>//=. 

  + by progress; smt.

  + by rewrite (consis3 (ValidProof(Cv)) Pe Ve Pz Vz G S (<:DecRel(Pe,Ve)) A AC2 AC3 v_distinct
           Verify_to_verify LPKE_prover_keepstate Prover_to_verify Prover_to_verify_left 
           validInd_ax Gi_ll Go_ll Pz_ll Vz_ll Si_ll So_ll Sp_ll A1_ll A2_ll AC2_ll AS_ll
           Vval_ll Vvot_ll Pe_ll Ve_ll C_ll relCons nonE_to_nonE enc_to_validInd &m).
  by sim. 
qed.

(* Lemma bounding STRONG CORRECTNESS *)
lemma scorr_bound (AS <: SCorr_Adv' { IPKE(Pe,Ve), Pz, Vz, Cv, HRO.RO, BSC, BS, G}) &m:
  Pr[SCorr(Heliosv3Mix(Pe, Ve, Cv, Pz, Vz), 
           AS(Heliosv3Mix(Pe, Ve, Cv, Pz, Vz)), HRO.RO, G).main() @ &m: BSC.valid] = 
`|Pr[Ind1CCA(IPKE(Pe,Ve), 
             INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, ValidProof(Cv)), 
                       AS(MV(IPKE(Pe,Ve), Pz, Vz, ValidProof(Cv))), G, HRO.RO)), 
             HRO.RO,Left).main() @ &m: res /\  size BS.encL <= 1] -
  Pr[Ind1CCA(IPKE(Pe,Ve), 
             INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, ValidProof(Cv)), 
                       AS(MV(IPKE(Pe,Ve), Pz, Vz, ValidProof(Cv))), G, HRO.RO)),
             HRO.RO,Right).main() @ &m: res /\  size BS.encL <= 1]|.
proof.  
  have ->: Pr[SCorr(Heliosv3Mix(Pe, Ve, Cv, Pz, Vz), 
                    AS(Heliosv3Mix(Pe, Ve, Cv, Pz, Vz)), 
                    HRO.RO, G).main() @ &m: BSC.valid] =
           Pr[SCorr(HeliosMix(Pe,Ve, ValidProof(Cv), Pz, Vz), 
                    AS(HeliosMix(Pe,Ve, ValidProof(Cv), Pz, Vz)), 
                    HRO.RO, G).main() @ &m: BSC.valid].
    by byequiv =>//=; sim.
  by rewrite (scorr(ValidProof(Cv)) Pe Ve Pz Vz G S (<:DecRel(Pe,Ve)) A AC2 AC3 v_distinct
                  Verify_to_verify LPKE_prover_keepstate Prover_to_verify Prover_to_verify_left 
                  validInd_ax Gi_ll Go_ll Pz_ll Vz_ll Si_ll So_ll Sp_ll A1_ll A2_ll AC2_ll AS_ll
                  Vval_ll Vvot_ll Pe_ll Ve_ll C_ll relCons nonE_to_nonE enc_to_validInd AS &m).
qed.

end section Security.