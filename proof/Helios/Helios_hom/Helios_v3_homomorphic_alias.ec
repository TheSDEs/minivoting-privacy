require import Option List Fun.
require (*  *) Helios_hom DiffieHellman.
require import Distr NewDistr Int FMap FSet Real Pair Mu_mem. 
require import LeftOrRight.

(* ###############################################################
   Helios version 3 with homomorphic tally and pseudonyms,
   obtain from Helios_hom with 
   -1. the label (Flabel)   = empty
   -2. Publish              = last ballot for each voter
   -3. tally operator (Rho) = addition over the last vote of a voter
   -4. relation (R)         = correct decryption
   -5. ValidInd             = check proof
   ############################################################### *)

  (* the space for the secret key and public key *)
  clone export CyclicGroup as Ksp.
  type skey = t.
  type pkey = group.

(*  ---------------------------------------------------------------------- *)
  (* voter identity: alias + uuid *)
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

  op Publish(bb: (ident * label * (h_cipher * h_prf* h_data)) list) = 
    map (fun (b: (ident * label * (h_cipher * h_prf* h_data))) => (b.`1.`1, b.`2, b.`3) ) 
    (keep_last bb).

(* ---------------------------------------------------------------------- *)
(* 3. Rho: addition( last vote policy)   *)

  (* last vote policy *)
  op Policy['a] (bb : (ident * 'a) list) =
    with bb = "[]"      => []
    with bb = (::) b bb => if   has (Fun.(\o) (pred1 b.`1) fst) bb
                         then Policy bb
                         else b :: Policy bb.

(* ---------------------------------------------------------------------- *)
(* 5. ValidInd - part 1 operator: check the proof using the operator verify *)
  (* op that creates a statement for the proof system used in encryption *)
    op to_statement: pkey -> label -> h_cipher -> h_stm.
    (* op that checks if proof for the statement used in encryption *)
    op verify : h_stm -> h_prf -> (h_in, h_out) map -> bool.
  op validInd (pk: pkey, b: (ident * label * (h_cipher* h_prf* h_data)), ro: (h_in, h_out) map) =
    verify (to_statement pk b.`2 b.`3.`1) b.`3.`2 ro.

clone export Helios_hom as Hv3H with
  type HH.label      <- label,
  type ident         <- ident,
  type HH.skey       <- skey,
  type HH.pkey       <- pkey,
  type HH.h_stm      <- h_stm,
  type HH.h_in       <- h_in,
  type HH.h_out      <- h_out,
  type HH.h_data     <- h_data,
  type HH.h_cipher   <- h_cipher,
  type HH.h_prf      <- h_prf,
  type HH.MV2.pubBB  <- (alias_name * label * (h_cipher * h_prf* h_data)) list,
  op HH.verify       <- verify,
  op HH.to_statement <- to_statement,
  op HH.MV2.Publish  <- Publish,
  op HH.MV2.Flabel   <- Flabel,
  op HH.MV2.validInd <- validInd,
  op Policy['a]      <- Policy.   

(* ---------------------------------------------------------------------- *)
(* 5. ValidInd - part 2 function: check the proof using the random oracle access *) 

  module ValidProof(Ve:PSpke.Verifier, H: Ipke.ARO) = {
    proc validInd( b: (ident * label * cipher), pk: pkey): bool ={
      var ev;
      ev <@ Ve(H).verify(to_statement pk b.`2 b.`3.`1, b.`3.`2);
      return ev;
    }
  }.

(* ---------------------------------------------------------------------- *)
(* 4. Relation (R): correct decryption  *)

module DecRel(Pe: PSpke.Prover, Ve: PSpke.Verifier, 
                    E: Scheme, H: HOracle.ARO) = DecRelation(E, H).
 
(* ---------------------------------------------------------------------- *)
(* Helios Version 3 with Homomorphic tally and true identities *) 
module Heliosv3H (Pe: PSpke.Prover, Ve: PSpke.Verifier, 
                  Ve2: PSpke.Verifier,
                  Pz: Prover,  Vz: Verifier,
                  H: HOracle.ARO,   G: GOracle.ARO)
   = HeliosHom(Pe, Ve, Pz, Vz, ValidProof(Ve2), H, G).

(* testing the reduction proof from Helios_v3_H to MiniVoting MV *)
section HomomorphicTally.

declare module Pe: PSpke.Prover   {BP, HRO.RO, SCorr_Oracle, BSC }.
declare module Ve: PSpke.Verifier {Pe, BSC, BP, HRO.RO}.
declare module Ve2: PSpke.Verifier {Pe, Ve, BSC, BP, HRO.RO}.

declare module Pz: Prover         {Pe, Ve, Ve2, BP, HRO.RO }.
declare module Vz: Verifier       {Pe, Ve, Ve2, Pz, BP, HRO.RO }.
declare module G : GOracle.Oracle {Pe, Ve, Ve2, Pz, Vz, BP, HRO.RO, BSC, SCorr_Oracle}.
declare module S : Simulator      {Pe, Ve, Ve2, Pz, Vz, G, BP, HRO.RO, BSC}.
declare module A : BPRIV_Adv      {Pe, Ve, Ve2, Pz, Vz, G, S, HRO.RO, BP }. 

(* ** ASSUMPTIONS ** *)
(* ** start *)
  (* axiom on transforming Ve.verify in verify operator *)
  axiom Verify_to_verify (gv: (glob Ve)) (s: h_stm) (p: h_prf):
    phoare[Ve(HRO.RO).verify: (glob Ve) = gv /\ arg = (s, p)
           ==>
           (glob Ve) = gv /\
           res = verify s p HRO.RO.m] = 1%r.
(* ** end *)

(* commutativity of policy and decryption *)
lemma san_tallymap (sbb: (ident * h_cipher) list) (sk: skey):
  let f = (fun (b : ident * h_cipher) =>
                (b.`1, (oget (decrypt sk b.`2)))) in
  Policy (map f sbb)  =
  map f (Policy sbb).
proof. 
  elim sbb =>//=.
  move => x l Hxl. 
  pose f:= (fun (b : ident * h_cipher) =>
                (b.`1, (oget (decrypt sk b.`2)))).
              
  have ->:  (has (pred1 (f x).`1 \o fst) (map f l)) = (has (pred1 x.`1 \o fst) l).
    rewrite has_map. 
    have ->: (preim f (pred1 (f x).`1 \o fst)) = (pred1 x.`1 \o fst).
      rewrite /preim. 
    rewrite /(\o) /pred1 //=.
    by smt.
  case (has (pred1 x.`1 \o fst) l); 
    move: Hxl; rewrite -/f; smt. 
qed.

(* membership of policy *)
lemma san_mem (sbb: (ident * h_cipher) list) (b: ident * h_cipher):
  mem (Policy sbb) b => mem sbb b.
proof.
  elim sbb =>//=.
  move => x sbb.
  by smt. 
qed.


(* reduction of this version of Helios to Minivoting *) 
equiv Hv3H2_MV_tally &m:
  MV(IPKE(Pe,Ve),Pz,Vz, ValidProof(Ve2), HRO.RO, G).tally ~
  Heliosv3H(Pe, Ve, Ve2, Pz, Vz, HRO.RO, G).tally  
  : ={glob HRO.RO, glob G, glob Pz, glob Pe, glob Ve, arg}  
      ==>
    ={res, glob HRO.RO, glob G, glob Pz, glob Pe, glob Ve}.
proof.
  progress. 
  by rewrite (MV_HA_tally (ValidProof(Ve2)) Pe Ve Pz Vz G S A
          san_tallymap san_mem Verify_to_verify). 
qed.

end section HomomorphicTally.

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
declare module AC2: SConsis2_Adv  {BP, HRO.RO, G, Cv}.
declare module AC3: SConsis3_Adv  {BP, HRO.RO, Pe, Ve, Pz, Cv, G}.

(* ** ASSUMPTIONS ** *)
(* ** start *)
  (* at least 2 distinct votes *)
  axiom v_distinct: v_def_0 <> v_def_1.
  
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

  axiom A1_ll (O <: BPRIV_Oracles {A}):
    islossless O.vote =>
    islossless O.cast =>
    islossless O.board =>
    islossless O.h => 
    islossless O.g => 
    islossless A(O).a1.
  axiom A2_ll (O <: BPRIV_Oracles {A}):
    islossless O.board =>
    islossless O.h => 
    islossless O.g => 
    islossless A(O).a2. 
  axiom AC2_ll (O <: SCons_Oracle {AC2}):
    islossless O.h => 
    islossless O.g => 
    islossless AC2(O).main.
  axiom AS_ll (AS <: SCorr_Adv') 
              (V<: VotingScheme {AS}) (O <: SCorr_Oracle {AS}):
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


  (* axiom linking Ve.verify to verify operator *)
  axiom Verify_to_verify (gv: (glob Ve)) (s: h_stm) (p: h_prf):
    phoare[Ve(HRO.RO).verify: (glob Ve) = gv /\ arg = (s, p)
           ==>
           (glob Ve) = gv /\
           res = verify s p HRO.RO.m] = 1%r.

  (* axiom linking Cv.verify to verify operator *)
  axiom Verify_to_verify' (gv: (glob Cv)) (s: h_stm) (p: h_prf):
    phoare[Cv(HRO.RO).verify: (glob Cv) = gv /\ arg = (s, p)
           ==>
           (glob Cv) = gv /\
           res = verify s p HRO.RO.m] = 1%r.

  (* axiom on state of prover *)
  axiom LPKE_prover_keepstate (gp: (glob Pe)) (H<: HOracle.ARO):
    phoare[Pe(H).prove: 
          (glob Pe) = gp ==> (glob Pe) = gp] = 1%r.

  (* axiom transforming proof in a verification (two-sided) *)
  axiom Prover_to_verify (s: h_stm) (w: h_wit):
    equiv[Pe(HRO.RO).prove ~ Pe(HRO.RO).prove: 
         ={glob HRO.RO, glob Pe, arg} /\ arg{1} = (s, w)
         ==>
         ={glob HRO.RO, glob Pe, res} /\
         verify s res{1} HRO.RO.m{1}].

  (* axiom transforming proof in a verification (one-sided) *)
  axiom Prover_to_verify_left (gp: (glob Pe)) (s: h_stm) (w: h_wit):
    phoare[Pe(HRO.RO).prove: 
           (glob Pe) = gp /\ arg = (s, w)
           ==>
           (glob Pe) = gp /\ verify s res HRO.RO.m]= 1%r.
(* ** end *)

local lemma validInd_ax (gc: (glob ValidProof(Cv))) (pk: pkey) (b: ident * label * cipher):
  phoare[ValidProof(Cv, HRO.RO).validInd: 
         (glob ValidProof(Cv)) = gc /\ arg = (b, pk) 
          ==>
          (glob ValidProof(Cv)) = gc /\ res = validInd pk b HRO.RO.m] = 1%r.
proof. 
  by proc; call (Verify_to_verify' gc (to_statement pk b.`2 b.`3.`1) b.`3.`2).
qed.

local lemma C_ll (H <: HOracle.ARO):
  islossless H.o => 
  islossless ValidProof(Cv, H).validInd.
proof.
  move => Ho; proc.   
  by call (Cv_ll H Ho). 
 qed.   

local lemma enc_to_validInd (pkx: pkey) (id: ident) (v: plain) (l : label):
  equiv[ IPKE(Pe,Ve,HRO.RO).enc ~ IPKE(Pe,Ve,HRO.RO).enc: 
         ={glob HRO.RO, glob IPKE(Pe,Ve), arg} /\ arg{1} = (pkx,l,v) 
         ==> ={res, glob IPKE(Pe,Ve), glob HRO.RO} /\
          validInd pkx (id, l, res{1}) HRO.RO.m{1}].
proof.
  proc.   
  seq 1 1: (={r, glob Pe, glob Ve, glob HRO.RO} /\
             (pk{1}, lbl{1}, p{1}) = (pk{2}, lbl{2}, p{2}) /\
             (pk{1}, lbl{1}, p{1}) = (pkx, l, v))=>//=;
    first by auto.
  sp; exists* l, c{1}, p{1}, r{1}; elim* => lblx c p r.
  call (Prover_to_verify (to_statement pkx lblx c) (to_witness p r)). 
  rewrite /validInd.
  by auto; progress; smt.
qed.

local lemma relCons (gh : (glob HRO.RO)):
    phoare[ DecRel(Pe, Ve, IPKE(Pe, Ve), HRO.RO).main :
             (glob HRO.RO) = gh ==> (glob HRO.RO) = gh] = 1%r.
proof.
  proc.
  inline*.
  wp; while (HRO.RO.m = gh) (size wit.`2 -i); progress.
    wp; call (Ve_ll HRO.RO HRO.RO_o_ll).
    by auto; progress; smt.
  by auto; progress; smt.
qed.

(* lemma bounding strong correctness, in bpriv *)
local lemma scorr_bpriv (LR<: LorR { BS, BP, BIND, BIND2, BSCorr, BSC, 
                                     HRO.RO, A, Ve, Cv, Vz, Pz, Pe, S}) &m:
  Pr[SCorr (Heliosv3H(Pe, Ve, Cv, Pz, Vz), 
            BSCorr(Heliosv3H(Pe, Ve, Cv, Pz, Vz),A, LR), 
            HRO.RO, S).main() @ &m: BSC.valid]  = 
`|Pr[Ind1CCA(IPKE(Pe,Ve),
             INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, ValidProof(Cv)), 
                       BSCorr(MV(IPKE(Pe,Ve),Pz,Vz, ValidProof(Cv)),A, LR), S, HRO.RO)),
             HRO.RO,Left).main() @ &m: res /\  size BS.encL <= 1] -
  Pr[Ind1CCA(IPKE(Pe,Ve),
             INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, ValidProof(Cv)),
                       BSCorr(MV(IPKE(Pe,Ve),Pz,Vz, ValidProof(Cv)),A, LR), S, HRO.RO)),
             HRO.RO,Right).main() @ &m: res /\  size BS.encL <= 1]|. 
proof. 
  have ->: Pr[SCorr (Heliosv3H(Pe, Ve, Cv, Pz, Vz), 
                     BSCorr(Heliosv3H(Pe, Ve, Cv, Pz, Vz),A, LR), 
                     HRO.RO, S).main() @ &m: BSC.valid] =
           Pr[SCorr (HeliosHom(Pe, Ve, Pz, Vz, ValidProof(Cv)), 
                     BSCorr(HeliosHom(Pe, Ve, Pz, Vz, ValidProof(Cv)),A, LR), 
                     HRO.RO, S).main() @ &m: BSC.valid].
    by byequiv =>//=; sim.

  by rewrite (scorr_bpriv (ValidProof(Cv)) Pe Ve Pz Vz (<: DecRel(Pe,Ve)) G S A AC2 AC3
         v_distinct Gi_ll Go_ll Si_ll So_ll Sp_ll C_ll Pz_ll Vz_ll Pe_ll Ve_ll A1_ll A2_ll 
         AC2_ll AS_ll Vval_ll Vvot_ll (san_tallymap Pe Ve Cv Pz Vz G S A Verify_to_verify)
         (san_mem Pe Ve Cv Pz Vz G S A Verify_to_verify) Verify_to_verify 
         LPKE_prover_keepstate Prover_to_verify Prover_to_verify_left validInd_ax 
         enc_to_validInd relCons LR &m). 
qed.

local lemma Rho_weight (x : (ident * fq option) list):
  weight (Rho x) = 1%r by smt.

(* vfr is 0 for this relation *) 
lemma bound_vfr (Gx <: GOracle.Oracle{BS, BP, HRO.RO, A, Ve, Pe, Cv}) &m:
  islossless Gx.init =>
  islossless Gx.o => 
  Pr[VFR(IPKE(Pe, Ve),BVFR(MV(IPKE(Pe, Ve),Pz,Vz,ValidProof(Cv)), A), 
         DecRel(Pe, Ve, IPKE(Pe, Ve)), HRO.RO, Gx).main() @ &m : res] = 0%r.
proof. 
  move => Gxi Gxo.
  cut T:= bound_vfr G S Vz Pz (ValidProof(Cv)) A Ve Pe A1_ll So_ll Si_ll Go_ll 
          Gi_ll C_ll Pe_ll Ve_ll Verify_to_verify Rho_weight Gx &m Gxi Gxo. 
 
  have ->: Pr[VFR(IPKE(Pe, Ve), 
                  BVFR(MV(IPKE(Pe, Ve), Pz, Vz, ValidProof(Cv)), A), 
                  DecRel(Pe,Ve,IPKE(Pe, Ve)), HRO.RO, Gx).main () @ &m : res] =
           Pr[VFR(IPKE(Pe, Ve), 
                  BVFR(MV(IPKE(Pe, Ve), Pz, Vz, ValidProof(Cv)), A), 
                  DecRelation(IPKE(Pe, Ve)), HRO.RO, Gx).main() @ &m : res].
    by byequiv =>//=; sim. 
  by apply T.
qed.

(* Lemma bounding bpriv *)
lemma bpriv &m: 
   `|Pr[BPRIV_L(Heliosv3H(Pe, Ve, Cv, Pz, Vz), A, HRO.RO, G).main() @ &m : res] -
     Pr[BPRIV_R(Heliosv3H(Pe, Ve, Cv, Pz, Vz), A, HRO.RO, G, S).main() @ &m :res]|
<=
   `|Pr[ZK_L(DecRelation(IPKE(Pe, Ve), HRO.RO), 
             Pz, BZK(IPKE(Pe, Ve), Pz, ValidProof(Cv), Vz, A, HRO.RO), G).main() @ &m : res] -
     Pr[ZK_R(DecRelation(IPKE(Pe, Ve), HRO.RO),
             S , BZK(IPKE(Pe, Ve), Pz, ValidProof(Cv), Vz, A, HRO.RO)).main() @ &m : res]| +
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
   `|Pr[Ind1CCA(IPKE(Pe, Ve), WrapAdv(BIND(MV(IPKE(Pe, Ve), Pz, Vz, ValidProof(Cv)), A, S), 
                                      IPKE(Pe, Ve), HRO.RO),
                HRO.RO, Left).main() @ &m : res /\ WrapAdv.l <= n /\ size BS.encL <= 1] -
     Pr[Ind1CCA(IPKE(Pe, Ve), WrapAdv(BIND(MV(IPKE(Pe, Ve), Pz, Vz, ValidProof(Cv)), A, S), 
                                      IPKE(Pe, Ve), HRO.RO), 
                HRO.RO, Right).main()@ &m : res /\ WrapAdv.l <= n /\ size BS.encL <= 1]|.
proof.
  have ->: Pr[BPRIV_L(Heliosv3H(Pe, Ve, Cv, Pz, Vz), A, HRO.RO, G).main() @ &m : res] =
           Pr[BPRIV_L(HeliosHom(Pe, Ve, Pz, Vz, ValidProof(Cv)), A, HRO.RO, G).main() @ &m : res].
    by byequiv =>//=; sim.
  have ->: Pr[BPRIV_R(Heliosv3H(Pe, Ve, Cv, Pz, Vz), A, HRO.RO, G, S).main() @ &m : res] =
           Pr[BPRIV_R(HeliosHom(Pe, Ve, Pz, Vz, ValidProof(Cv)), A, HRO.RO, G, S).main() @ &m : res].
    by byequiv =>//=; sim.
    
  cut oldbpriv:= bpriv (ValidProof(Cv)) Pe Ve Pz Vz (<: DecRel(Pe,Ve)) G S A AC2 AC3
         v_distinct Gi_ll Go_ll Si_ll So_ll Sp_ll C_ll Pz_ll Vz_ll Pe_ll Ve_ll A1_ll A2_ll 
         AC2_ll AS_ll Vval_ll Vvot_ll (san_tallymap Pe Ve Cv Pz Vz G S A Verify_to_verify)
         (san_mem Pe Ve Cv Pz Vz G S A Verify_to_verify) Verify_to_verify LPKE_prover_keepstate
         Prover_to_verify Prover_to_verify_left validInd_ax enc_to_validInd relCons &m. 
  (* make the VFR experiment 0 *)
  rewrite (bound_vfr G &m Gi_ll Go_ll) in oldbpriv.
  rewrite (bound_vfr S &m Si_ll So_ll) in oldbpriv.

  (* make the scorr equal to ind1cca *)
  move: oldbpriv.
  have ->: Pr[SCorr(MV(IPKE(Pe, Ve), Pz, Vz, ValidProof(Cv)), 
              BSCorr(MV(IPKE(Pe, Ve), Pz, Vz, ValidProof(Cv)), A, Left), 
              HRO.RO, S).main() @ &m : BSC.valid] = 
           Pr[SCorr (Heliosv3H(Pe, Ve, Cv, Pz, Vz), 
              BSCorr(Heliosv3H(Pe, Ve, Cv, Pz, Vz),A, Left), 
              HRO.RO, S).main() @ &m: BSC.valid].
    by byequiv =>//=; sim.
  rewrite (scorr_bpriv Left &m).
  have ->: Pr[SCorr(MV(IPKE(Pe, Ve), Pz, Vz, ValidProof(Cv)), 
              BSCorr(MV(IPKE(Pe, Ve), Pz, Vz, ValidProof(Cv)), A, Right), 
              HRO.RO, S).main() @ &m : BSC.valid] = 
           Pr[SCorr (Heliosv3H(Pe, Ve, Cv, Pz, Vz), 
              BSCorr(Heliosv3H(Pe, Ve, Cv, Pz, Vz),A, Right), 
              HRO.RO, S).main() @ &m: BSC.valid].
    by byequiv =>//=; sim.
  by rewrite (scorr_bpriv Right &m).
qed.


(* Lemma bounding STRONG CONSITENCY *) 
lemma consis1(id: ident, v: plain, l: label) &m: 
   Pr[SConsis1(Heliosv3H(Pe, Ve, Cv, Pz, Vz), CE(IPKE(Pe,Ve)), HRO.RO, G).main(id,v, l) @ &m: res]  >=
   Pr[PKEvf.Correctness(IPKE(Pe,Ve), HRO.RO).main(v,l) @ &m: res].
proof.
  have ->: Pr[SConsis1(Heliosv3H(Pe, Ve, Cv, Pz, Vz), 
                       CE(IPKE(Pe,Ve)), HRO.RO, G).main(id,v, l) @ &m: res] =
           Pr[SConsis1(HeliosHom(Pe, Ve, Pz, Vz, ValidProof(Cv)), 
                       CE(IPKE(Pe,Ve)), HRO.RO, G).main(id,v, l) @ &m: res].
    by byequiv =>//=; sim.

  by rewrite (consis1 (ValidProof(Cv)) Pe Ve Pz Vz (<: DecRel(Pe,Ve)) G S A AC2 AC3
         v_distinct Gi_ll Go_ll Si_ll So_ll Sp_ll C_ll Pz_ll Vz_ll Pe_ll Ve_ll A1_ll A2_ll 
         AC2_ll AS_ll Vval_ll Vvot_ll (san_tallymap Pe Ve Cv Pz Vz G S A Verify_to_verify)
         (san_mem Pe Ve Cv Pz Vz G S A Verify_to_verify) Verify_to_verify LPKE_prover_keepstate
         Prover_to_verify Prover_to_verify_left validInd_ax enc_to_validInd relCons id v l &m). 
qed.

lemma consis2 &m:
  Pr[SConsis2(Heliosv3H(Pe, Ve, Cv, Pz, Vz), ValidProof(Cv), AC2, HRO.RO, G).main() @ &m: res] = 1%r.
proof. 
  have ->: Pr[SConsis2(Heliosv3H(Pe, Ve, Cv, Pz, Vz), 
                       ValidProof(Cv), AC2, HRO.RO, G).main() @ &m: res] =
           Pr[SConsis2(HeliosHom(Pe, Ve, Pz, Vz, ValidProof(Cv)), 
                       ValidProof(Cv), AC2, HRO.RO, G).main() @ &m: res].
    by byequiv =>//=; sim.

  by rewrite (consis2 (ValidProof(Cv)) Pe Ve Pz Vz (<: DecRel(Pe,Ve)) G S A AC2 AC3
         v_distinct Gi_ll Go_ll Si_ll So_ll Sp_ll C_ll Pz_ll Vz_ll Pe_ll Ve_ll A1_ll A2_ll 
         AC2_ll AS_ll Vval_ll Vvot_ll (san_tallymap Pe Ve Cv Pz Vz G S A Verify_to_verify)
         (san_mem Pe Ve Cv Pz Vz G S A Verify_to_verify) Verify_to_verify LPKE_prover_keepstate
         Prover_to_verify Prover_to_verify_left validInd_ax enc_to_validInd relCons &m).
qed.

equiv consis3 &m:
    SConsis3_L(Heliosv3H(Pe, Ve, Cv, Pz, Vz), ValidProof(Cv), AC3, HRO.RO, G).main ~ 
    SConsis3_R(Heliosv3H(Pe, Ve, Cv, Pz, Vz), CE(IPKE(Pe,Ve)), ValidProof(Cv), AC3, HRO.RO, G).main
    : ={glob HRO.RO, glob G, glob IPKE(Pe,Ve), glob ValidProof(Cv), glob Pz, glob AC3} ==> ={res}.
proof.
  transitivity SConsis3_L(HeliosHom(Pe, Ve, Pz, Vz, ValidProof(Cv)), 
                          ValidProof(Cv), AC3, HRO.RO, G).main 
  (={glob HRO.RO, glob G, glob IPKE(Pe,Ve), glob ValidProof(Cv), glob Pz, glob AC3} ==> 
   ={res})
  (={glob HRO.RO, glob G, glob IPKE(Pe,Ve), glob ValidProof(Cv), glob Pz, glob AC3} ==> 
   ={res})=>//=. 

  + by progress; smt.
  + by proc; sim. 
  
  transitivity SConsis3_R(HeliosHom(Pe, Ve, Pz, Vz, ValidProof(Cv)), 
                          CE(IPKE(Pe,Ve)), ValidProof(Cv), AC3, HRO.RO, G).main 
  (={glob HRO.RO, glob G, glob IPKE(Pe,Ve), glob ValidProof(Cv), glob Pz, glob AC3} ==> 
   ={res})
  (={glob HRO.RO, glob G, glob IPKE(Pe,Ve), glob ValidProof(Cv), glob Pz, glob AC3} ==> 
   ={res})=>//=. 

  + by progress; smt.

  + conseq (_: ={glob HRO.RO, glob G, glob IPKE(Pe, Ve), 
                 glob ValidProof(Cv), glob Pz, glob AC3} ==> _)=>//=. 
    by rewrite (consis3 (ValidProof(Cv)) Pe Ve Pz Vz (<: DecRel(Pe,Ve)) G S A AC2 AC3
         v_distinct Gi_ll Go_ll Si_ll So_ll Sp_ll C_ll Pz_ll Vz_ll Pe_ll Ve_ll A1_ll A2_ll 
         AC2_ll AS_ll Vval_ll Vvot_ll (san_tallymap Pe Ve Cv Pz Vz G S A Verify_to_verify)
         (san_mem Pe Ve Cv Pz Vz G S A Verify_to_verify) Verify_to_verify LPKE_prover_keepstate
         Prover_to_verify Prover_to_verify_left validInd_ax enc_to_validInd relCons  &m). 

  by sim. 
qed.

(* Lemma bounding STRONG CORRECTNESS *)
lemma scorr (AS <: SCorr_Adv' { IPKE(Pe,Ve), Pz, Vz, Cv, HRO.RO, BSC, BS, G}) &m:
  Pr[SCorr(Heliosv3H(Pe, Ve, Cv, Pz, Vz), 
           AS(Heliosv3H(Pe, Ve, Cv, Pz, Vz)), HRO.RO, G).main() @ &m: BSC.valid] = 
`|Pr[Ind1CCA(IPKE(Pe,Ve), 
             INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, ValidProof(Cv)), 
                       AS(MV(IPKE(Pe,Ve), Pz, Vz, ValidProof(Cv))), G, HRO.RO)), 
             HRO.RO,Left).main()  @ &m: res /\  size BS.encL <= 1] -
  Pr[Ind1CCA(IPKE(Pe,Ve), 
             INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, ValidProof(Cv)), 
                       AS(MV(IPKE(Pe,Ve), Pz, Vz, ValidProof(Cv))), G, HRO.RO)),
             HRO.RO,Right).main()  @ &m: res /\  size BS.encL <= 1]|.
proof.  
  have ->: Pr[SCorr(Heliosv3H(Pe, Ve, Cv, Pz, Vz), 
                    AS(Heliosv3H(Pe, Ve, Cv, Pz, Vz)), 
                    HRO.RO, G).main() @ &m: BSC.valid] =
           Pr[SCorr(HeliosHom(Pe, Ve, Pz, Vz, ValidProof(Cv)), 
                   AS(HeliosHom(Pe, Ve, Pz, Vz, ValidProof(Cv))), 
                   HRO.RO, G).main () @ &m : BSC.valid].
    by byequiv =>//=; sim.

  by exact (scorr_bound (ValidProof(Cv)) Pe Ve Pz Vz (<: DecRel(Pe,Ve)) G S A AC2 AC3
         v_distinct Gi_ll Go_ll Si_ll So_ll Sp_ll C_ll Pz_ll Vz_ll Pe_ll Ve_ll A1_ll A2_ll 
         AC2_ll AS_ll Vval_ll Vvot_ll (san_tallymap Pe Ve Cv Pz Vz G S A Verify_to_verify)
         (san_mem Pe Ve Cv Pz Vz G S A Verify_to_verify) Verify_to_verify LPKE_prover_keepstate
         Prover_to_verify Prover_to_verify_left validInd_ax enc_to_validInd relCons AS G &m 
         Gi_ll Go_ll). 
qed.

end section Security.