require import Option List Fun.
require (*  *) Helios_hom.
require import Distr NewDistr Int FMap FSet Real Pair Mu_mem. 
require import LeftOrRight.


clone export Helios_hom as HW.

(* ---------------------------------------------------------------------- *)
(* HeliosHom with light weeding *) 
module HeliosHomWeed (Pe: PSpke.Prover, Ve: PSpke.Verifier, 
                      Pz: Prover,  Vz: Verifier, C: ValidInd,
                      H: HOracle.ARO,   G: GOracle.ARO)  ={

  proc setup  = HeliosHom(Pe, Ve, Pz, Vz, C , H, G).setup
  proc vote   = HeliosHom(Pe, Ve, Pz, Vz, C, H, G).vote
  proc tally  = HeliosHom(Pe, Ve, Pz, Vz, C, H, G).tally
  proc verify = HeliosHom(Pe, Ve, Pz, Vz, C, H, G).verify

  proc valid  = MV'(IPKE(Pe, Ve), Pz, Vz, C, H, G).valid
}.


(* Security Properties: BPRIV, Strong Consistency, Strong Correctness *)
section Security.

declare module C : ValidInd       {BP, BS, BPS, BSC, BSCorr, BIND, HRO.RO,
                                   BPRIV_SB, BIND2, PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv}. 
declare module Pe: PSpke.Prover   {C, BS, BP, BSC, BSCorr, HRO.RO, SCorr_Oracle, BPS, BIND,
                                   PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv, BPRIV_SB, BIND2 }.
declare module Ve: PSpke.Verifier {C, BS, BP, BSC, BSCorr, Pe, HRO.RO, BPS, BIND,
                                   PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv, BPRIV_SB, BIND2}.

declare module Pz: Prover         {C, Pe, Ve, BP, BS, BSCorr, BIND, HRO.RO, BPS, BSC }.
declare module Vz: Verifier       {C, Pe, Ve, Pz, BP, BS, BSCorr, BIND, HRO.RO, BPS, BSC }.
declare module Rz: VotingRelation' {BPS, BP, BS, C, Pz, Vz, Ve, Pe, HRO.RO}.
declare module G : GOracle.Oracle {C, Pe, Ve, Pz, Vz, BP, Rz, HRO.RO, BSC, BPS, BS, BIND, 
                                   BSCorr, SCorr_Oracle}.
declare module S : Simulator      {C, Pe, Ve, Pz, Vz, G, Rz, BS, BP, BSC, BSCorr, HRO.RO, BSC, BPS,
                                   BPRIV_SB, BIND2, BIND, PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv}.

(* adversary models *)
declare module A : BPRIV_Adv      {C, Pe, Ve, Pz, Vz, Rz, G, S, HRO.RO, BP, BS, BSCorr, BSC, BPS,
                                   PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv, BPRIV_SB, BIND, BIND2 }.
declare module AC2: SConsis2_Adv {BP, HRO.RO, G, C}.
declare module AC3: SConsis3_Adv {BP, HRO.RO, Pe, Ve, Pz, C, G}.

(* ** ASSUMPTIONS ** *)
(* ** start *)
  (* injectivity on Flabel *)
  axiom Finj (x y : ident): 
    Flabel x = Flabel y => x = y.
  (* at least 2 distinct votes *)
  axiom v_distinct: v_def_0 <> v_def_1.

  (* lossless *)
  axiom Gi_ll: islossless G.init.
  axiom Go_ll: islossless G.o.

  axiom Si_ll: islossless S.init.
  axiom So_ll: islossless S.o.
  axiom Sp_ll: islossless S.prove.

  axiom C_ll (H <: HOracle.ARO):
    islossless H.o => 
    islossless C(H).validInd.

  axiom Pp_ll (G <: GOracle.ARO):
    islossless G.o => 
    islossless Pz(G).prove.
  axiom Vv_ll (G <: GOracle.ARO):
    islossless G.o => 
    islossless Vz(G).verify.

  axiom Pe_ll (H<: HOracle.ARO):
    islossless H.o=>
    islossless Pe(H).prove.
  axiom Ve_ll (H<: HOracle.ARO):
    islossless H.o=>
    islossless Ve(H).verify.

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
  axiom AC_ll (AS <: SCorr_Adv') 
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

  (* axiom on commutativity of policy and decryption *)
  axiom san_tallymap (sbb: (ident * h_cipher) list) (sk: skey):
    let f = (fun (b : ident * h_cipher) =>
                (b.`1, (oget (decrypt sk b.`2)))) in
  Policy (map f sbb)  =  map f (Policy sbb).

  (* axiom on membership of policy  *)
  axiom san_mem (sbb: (ident * h_cipher) list) (b: ident * h_cipher):
    mem (Policy sbb) b => mem sbb b.

  (* axiom linking Ve.verify to verify operator *)
  axiom Verify_to_verify (gv: (glob Ve)) (s: h_stm) (p: h_prf):
    phoare[Ve(HRO.RO).verify: (glob Ve) = gv  /\ arg = (s, p)
         ==>
         (glob Ve) = gv /\ 
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

  (* axiom linking C.validInd to validInd operator *)
  axiom validInd_ax (gc : (glob C)) (pk : pkey) (b : ident * label * cipher):
    phoare[C(HRO.RO).validInd :
          (glob C) = gc /\ arg = (b, pk) 
           ==>
          (glob C) = gc /\ res = validInd pk b HRO.RO.m] = 1%r.

  (* encryption always implies validInd true *)
  axiom enc_to_validInd (pkx: pkey) (id: ident) (v: plain) (l : label):
    equiv[IPKE(Pe,Ve,HRO.RO).enc ~ IPKE(Pe,Ve,HRO.RO).enc: 
         ={glob HRO.RO, glob IPKE(Pe,Ve), arg} /\ arg{1} = (pkx,l,v) 
         ==> 
         ={res, glob IPKE(Pe,Ve), glob HRO.RO} /\
          validInd pkx (id, l, res{1}) HRO.RO.m{1}].

  (* axiom on a voting relation that does not 
     change the eager random oracle state *)
  axiom relConstraint (gh : (glob HRO.RO)):
    phoare[ Rz(IPKE(Pe,Ve), HRO.RO).main : 
          (glob HRO.RO) = gh ==> (glob HRO.RO) = gh] = 1%r.
(* ** end *)

 
(* valid equivalence, in the context of strong correctness adversary *)
equiv valid_light (LR<: LorR { HRO.RO, C}) (Gx <: GOracle.ARO { HRO.RO, C})
            (bbx: (ident * label * cipher) list) (uLx: (ident, label) map) 
            (bx: ident * label * cipher) (pkx: pkey):
  BSCorr(HeliosHomWeed(Pe, Ve, Pz, Vz, C), A, LR, 
         SCorr_Oracle(HeliosHomWeed(Pe, Ve, Pz, Vz,C), HRO.RO, S)).V.valid ~ 
  BSCorr(HeliosHom(Pe, Ve, Pz, Vz, C), A, LR, 
         SCorr_Oracle(HeliosHom(Pe, Ve, Pz, Vz, C), HRO.RO, S)).V.valid
 : ={glob HRO.RO, glob C, arg} /\ arg{2} = (bbx, uLx, bx, pkx) /\
    (forall b, mem bbx b => oget uLx.[b.`1] = b.`2/\ uLx.[b.`1] <> None) /\
    (forall id id', (uLx.[id] <> None /\ uLx.[id'] <> None) 
                     => oget uLx.[id] = oget uLx.[id'] => id = id')
   ==>
   ={res, glob HRO.RO, glob C}/\
   (res{2} =>  uLx.[bx.`1] <> None /\ oget uLx.[bx.`1] = bx.`2). 
proof.

  cut T:= same_valid C Pz Vz G HRO.RO S A Ve Pe Finj v_distinct enc_to_validInd
                     validInd_ax  Prover_to_verify_left Prover_to_verify Verify_to_verify
                     Pe_ll Ve_ll So_ll Si_ll AC_ll Gx bbx uLx bx pkx.
  symmetry.
  
  transitivity MV(IPKE(Pe, Ve), Pz, Vz, C, HRO.RO, Gx).valid 
  (={glob HRO.RO, glob C, arg} /\ arg{2} = (bbx, uLx, bx, pkx) /\
    (forall b, mem bbx b => oget uLx.[b.`1] = b.`2 /\ uLx.[b.`1] <> None) /\
    (forall id id', uLx.[id] <> None /\ uLx.[id'] <> None 
                    => oget uLx.[id] = oget uLx.[id'] => id = id')
    ==>
    ={res, glob HRO.RO, glob C} /\ 
    (res{2} => uLx.[bx.`1] <> None /\ oget uLx.[bx.`1] = bx.`2))
  (={glob HRO.RO, glob C, arg} /\ arg{2} = (bbx, uLx, bx, pkx) /\
    (forall b, mem bbx b => oget uLx.[b.`1] = b.`2 /\ uLx.[b.`1] <> None) /\
    (forall id id', uLx.[id] <> None /\ uLx.[id'] <> None 
                    => oget uLx.[id] = oget uLx.[id'] => id = id')
     ==>
     ={res, glob HRO.RO, glob C} /\
    (res{2} => uLx.[bx.`1] <> None /\ oget uLx.[bx.`1] = bx.`2))=>//=.
 
  + progress; smt.
  + proc; inline *. 
    wp; call (_: ={glob HRO.RO}); first by sim.
    wp; while (={ i, bb, ev1, b}).
      by auto; progress; smt.
    by auto; progress; smt.

  transitivity MV'(IPKE(Pe, Ve), Pz, Vz, C, HRO.RO, Gx).valid 
  (={glob HRO.RO, glob C, arg} /\ arg{2} = (bbx, uLx, bx, pkx) /\
   (forall b, mem bbx b => oget uLx.[b.`1] = b.`2 /\ uLx.[b.`1] <> None) /\
   (forall id id', uLx.[id] <> None /\ uLx.[id'] <> None 
                   => oget uLx.[id] = oget uLx.[id'] => id = id')
    ==>
   ={res, glob HRO.RO, glob C} /\ 
   (res{2} => uLx.[bx.`1] <> None /\ oget uLx.[bx.`1] = bx.`2))
  (={glob HRO.RO, glob C, arg} /\ arg{2} = (bbx, uLx, bx, pkx) /\
   (forall b, mem bbx b => oget uLx.[b.`1] = b.`2 /\ uLx.[b.`1] <> None) /\
   (forall id id', uLx.[id] <> None /\ uLx.[id'] <> None 
                   => oget uLx.[id] = oget uLx.[id'] => id = id')
   ==>
   ={res, glob HRO.RO, glob C} /\ 
   (res{2} => uLx.[bx.`1] <> None /\ oget uLx.[bx.`1] = bx.`2))=>//=. 

  + progress; smt.
  
  proc; inline *.
  wp; call (_: = {glob HRO.RO}).
    by sim.
  by auto.
qed.

(* valid equivalence  *)
equiv valid_less2 (LR<: LorR { HRO.RO, C}) (Gx <: GOracle.ARO { HRO.RO, C})
            (bbx: (ident * label * cipher) list) (uLx: (ident, label) map) 
            (bx: ident * label * cipher)  (pkx: pkey):
  HeliosHomWeed(Pe, Ve, Pz, Vz, C, HRO.RO, Gx).valid ~
  HeliosHom(Pe, Ve, Pz, Vz, C, HRO.RO, Gx).valid
   : ={glob HRO.RO, glob C, arg} /\ arg{2} = (bbx, uLx, bx, pkx) /\
    (forall b, mem bbx b => oget uLx.[b.`1] = b.`2/\ uLx.[b.`1] <> None) /\
    (forall id id', (uLx.[id] <> None /\ uLx.[id'] <> None) 
                     => oget uLx.[id] = oget uLx.[id'] => id = id')
      ==>
    ={res, glob HRO.RO, glob C}/\  
    (res{2} =>  uLx.[bx.`1] <> None /\ oget uLx.[bx.`1] = bx.`2). 
proof.

  cut T:= valid_light LR Gx bbx uLx bx pkx. 
  transitivity BSCorr(HeliosHomWeed(Pe, Ve, Pz, Vz, C), A, LR, 
                      SCorr_Oracle(HeliosHomWeed(Pe, Ve, Pz, Vz, C), HRO.RO, S)).V.valid 
  (={glob HRO.RO, glob C, arg} /\ arg{2} = (bbx, uLx, bx, pkx) /\
   (forall b, mem bbx b => oget uLx.[b.`1] = b.`2 /\ uLx.[b.`1] <> None) /\
   (forall id id', uLx.[id] <> None /\ uLx.[id'] <> None 
                   => oget uLx.[id] = oget uLx.[id'] => id = id')
   ==>
   ={res, glob HRO.RO, glob C} /\ 
   (res{2} => uLx.[bx.`1] <> None /\ oget uLx.[bx.`1] = bx.`2))
  (={glob HRO.RO, glob C, arg} /\ arg{2} = (bbx, uLx, bx, pkx) /\
   (forall b, mem bbx b => oget uLx.[b.`1] = b.`2 /\ uLx.[b.`1] <> None) /\
   (forall id id', uLx.[id] <> None /\ uLx.[id'] <> None 
                   => oget uLx.[id] = oget uLx.[id'] => id = id')
   ==>
   ={res, glob HRO.RO, glob C} /\ 
   (res{2} => uLx.[bx.`1] <> None /\ oget uLx.[bx.`1] = bx.`2))=>//=.

  + progress; smt.
  + proc; inline *.
    wp; call (_: ={glob HRO.RO}).
      by sim.
    by auto; progress; smt. 

  symmetry.
  transitivity 
  BSCorr(HeliosHom(Pe, Ve, Pz, Vz, C), A, LR, 
         SCorr_Oracle(HeliosHom(Pe, Ve, Pz, Vz, C), HRO.RO, S)).V.valid 
  (={glob HRO.RO, glob C, arg} /\ arg{2} = (bbx, uLx, bx, pkx) /\
   (forall b, mem bbx b => oget uLx.[b.`1] = b.`2 /\ uLx.[b.`1] <> None) /\
   (forall id id', uLx.[id] <> None /\ uLx.[id'] <> None 
                   => oget uLx.[id] = oget uLx.[id'] => id = id')
   ==>
   ={res, glob HRO.RO, glob C} /\ 
   (res{2} => uLx.[bx.`1] <> None /\ oget uLx.[bx.`1] = bx.`2))
  (={glob HRO.RO, glob C, arg} /\ arg{2} = (bbx, uLx, bx, pkx) /\
   (forall b, mem bbx b => oget uLx.[b.`1] = b.`2 /\ uLx.[b.`1] <> None) /\
   (forall id id', uLx.[id] <> None /\ uLx.[id'] <> None 
                   => oget uLx.[id] = oget uLx.[id'] => id = id')
   ==>
   ={res, glob HRO.RO, glob C} /\ 
   (res{2} => uLx.[bx.`1] <> None /\ oget uLx.[bx.`1] = bx.`2))=>//=.

  + progress; smt.
  + proc; inline *.
    wp; call (_: ={glob HRO.RO}).
      by sim.
    wp; while (={ i, bb, ev1, b}).
      by auto; progress; smt.
    by auto; progress; smt.

  symmetry. 
  move: T; simplify; move => T. 
  conseq (_: ={HRO.RO.m, glob C, arg} /\ arg{2} = (bbx, uLx, bx, pkx) /\
            (forall b, mem bbx b => oget uLx.[b.`1] = b.`2 /\ uLx.[b.`1] <> None) /\
            (forall id id', uLx.[id] <> None /\ uLx.[id'] <> None
                            => oget uLx.[id] = oget uLx.[id'] => id = id') ==>
            ={res, HRO.RO.m, glob C} /\ 
            (res{2} => uLx.[bx.`1] <> None /\ oget uLx.[bx.`1] = bx.`2)) ;
         first 2 by progress.
  by apply T.
qed. 

(* strong correctness of HeliosHomWeed reduced to HeliosHom, for adversary BSCorr *)
lemma scorr_HeliosHomWeed_HeliosHom 
      (LR<: LorR { BS, BP, BIND, BIND2, BSCorr, BSC, 
                   HRO.RO, A, Ve, C, Vz, Pz, Pe, S, G}) &m:
  Pr[SCorr (HeliosHomWeed(Pe, Ve, Pz, Vz, C), 
            BSCorr(HeliosHomWeed(Pe, Ve, Pz, Vz, C),A, LR), HRO.RO, S).main() @ &m: BSC.valid] =
  Pr[SCorr (HeliosHom(Pe, Ve, Pz, Vz, C), 
            BSCorr(HeliosHom(Pe, Ve, Pz, Vz, C),A, LR), HRO.RO, S).main() @ &m: BSC.valid]. 
proof.
  byequiv(_: ={glob A, glob S, glob Pe, glob C, glob Ve, glob Pz, glob Vz} ==> _) =>//=. 
  proc.
  inline SCorr(HeliosHomWeed(Pe, Ve, Pz, Vz, C), 
               BSCorr(HeliosHomWeed(Pe, Ve, Pz, Vz, C), A, LR), HRO.RO, S).A.main
         SCorr(HeliosHom(Pe, Ve, Pz, Vz, C), 
               BSCorr(HeliosHom(Pe, Ve, Pz, Vz, C), A, LR), HRO.RO, S).A.main.
  
  call (_: ={glob HRO.RO, glob Pz, glob Vz, glob IPKE(Pe,Ve), glob C, 
             BSCorr.ibad, BSCorr.bb, BSC.pk, BP.uL, BP.pk, BSC.qt, BSC.uL, BSC.valid,
             BP.qVo, BP.qCa, glob S }/\
             BSC.uL{1} = BP.uL{1} /\
           (forall b, mem BSCorr.bb{2} b => oget BP.uL{2}.[b.`1] = b.`2 /\ BP.uL{2}.[b.`1] <> None) /\
           (forall id id', (BP.uL{2}.[id] <> None /\ BP.uL{2}.[id'] <> None) =>
                           oget BP.uL{2}.[id] = oget BP.uL{2}.[id'] => id = id')).
    + proc. 
      if =>//=. 
      sp; if; auto.
      seq 4 4 : (={id, v0, v1, glob HRO.RO, glob Pz, glob Vz, glob S, glob IPKE(Pe,Ve), 
                   glob C, BP.uL,BSC.valid, BP.pk, BP.qVo, BP.qCa, BSCorr.ibad, BSCorr.bb, 
                   BSC.qt, BSC.uL, BSC.pk} /\
                 BSC.uL{1} = BP.uL{1} /\
                 (forall b2, mem BSCorr.bb{2} b2 => oget BP.uL{2}.[b2.`1] = b2.`2 /\ 
                                                    BP.uL{2}.[b2.`1] <> None) /\
                 (forall id id', (BP.uL{2}.[id] <> None /\ BP.uL{2}.[id'] <> None) =>
                                 oget BP.uL{2}.[id] = oget BP.uL{2}.[id'] => id = id')/\
                 ={b} /\ b{2}.`1 = id{2}).
      + inline *.
        wp; call(_: ={glob HRO.RO}). 
          by sim.
        auto; call (_: true).
        by auto; progress; smt. 
   
      exists* BSCorr.bb{2}, BP.uL{2}, b{2}, BP.pk{2}; elim* => bbx uLx bx pkx.
      call (valid_light LR S bbx uLx bx pkx). 
      by auto; progress; smt.
  
      if=>//=.
      inline SCorr_Oracle(HeliosHomWeed(Pe, Ve, Pz, Vz, C), HRO.RO, S).test
             SCorr_Oracle(HeliosHom(Pe, Ve, Pz, Vz, C), HRO.RO, S).test.
      seq 5 5: (={id, v0, v1, glob HRO.RO, glob Pz, glob Vz, BSC.valid, glob IPKE(Pe,Ve), 
                  glob C, BP.uL, BSC.pk, BP.pk, BP.qVo, BP.qCa, BSCorr.ibad, BSCorr.bb, 
                  BSC.qt, BSC.uL, glob S} /\
                BSC.uL{1} = BP.uL{1} /\
                (forall b2, mem BSCorr.bb{2} b2 => oget BP.uL{2}.[b2.`1] = b2.`2/\ 
                                                   BP.uL{2}.[b2.`1] <> None) /\
                (forall id id', (BP.uL{2}.[id] <> None /\ BP.uL{2}.[id'] <> None) =>
                                oget BP.uL{2}.[id] = oget BP.uL{2}.[id'] => id = id')/\
                ={bb, v2, id0} /\ bb{1} = BSCorr.bb{1} /\ id0{1} = id{1} /\ v2{1} = v{1}).
        + by wp; call(_: true); auto.         
      if =>//=; last by auto.
      if =>//=; last by auto.
      sp; if=>//=; last by auto.  

      seq 2 2: (={id, v0, v1, glob HRO.RO, glob Pz, glob Vz, BSC.valid, glob IPKE(Pe,Ve), 
                  glob C, BP.uL, BP.pk, BP.qVo, BP.qCa, BSCorr.ibad, BSCorr.bb, BSC.qt, 
                  BSC.uL, BSC.pk, glob S} /\
                BSC.uL{1} = BP.uL{1} /\
                (forall b2, mem BSCorr.bb{2} b2 => oget BP.uL{2}.[b2.`1] = b2.`2/\
                                                   BP.uL{2}.[b2.`1] <> None) /\
                (forall id id', (BP.uL{2}.[id] <> None /\ BP.uL{2}.[id'] <> None) =>
                                oget BP.uL{2}.[id] = oget BP.uL{2}.[id'] => id = id')/\
                ={bb, v2, id0, b0} /\ bb{1} = BSCorr.bb{1} /\ id0{1} = id{1} /\ 
                v2{1} = v{1}/\ b0{1}.`1 = id{1}).
        + inline *.
          wp; call(_: ={glob HRO.RO}). 
            by sim.
          by auto; progress; smt. 
 
      exists* BSCorr.bb{2}, BSC.uL{2}, b0{2}, BSC.pk{2}; elim* => bbx uLx bx pkx.
      wp; call (valid_less2 LR S bbx uLx bx pkx). 
      by auto; progress; smt.


    + proc. 
      if; auto.   
      exists* BSCorr.bb{2}, BP.uL{2}, b{2}, BP.pk{2}; elim* => bbx uLx bx pkx.
      call (valid_light LR G bbx uLx bx pkx).
      by auto; progress; smt.

    + proc; inline*; auto. 
    + proc; auto.
    + have So: equiv [S.o ~ S.o : ={arg, glob S} ==> ={res, glob S}]
        by proc true; first 2 by progress.
      conseq So=>//=. 
  
  auto. 
  inline SCorr(HeliosHomWeed(Pe, Ve, Pz, Vz, C), 
               BSCorr(HeliosHomWeed(Pe, Ve, Pz, Vz, C), A, LR), HRO.RO, S).V.setup
         SCorr(HeliosHom(Pe, Ve, Pz, Vz, C), 
               BSCorr(HeliosHom(Pe, Ve, Pz, Vz, C), A, LR), HRO.RO, S).V.setup.
  wp; while (={i, nr, uL0}/\
             (forall id id', (uL0{2}.[id] <> None /\ uL0{2}.[id'] <> None) =>
                             oget uL0{2}.[id] = oget uL0{2}.[id'] => id = id')/\
             (forall idx, uL0{2}.[idx] <> None => oget uL0{2}.[idx] = Flabel idx)).
    auto; progress. 
    + case (idL = id0).
      + case (idL = id'). 
        + by smt. 
        - move => Hx1 Hx2. 
          move: H7. 
          have ->: oget uL0{2}.[idL <- Flabel idL].[id'] = oget uL0{2}.[id'] by smt.  
          rewrite (H0 id' _); first by smt.  
          have ->: oget uL0{2}.[idL <- Flabel idL].[id0] = Flabel id0 by smt.  
          by smt.
      - case (idL <> id').
        + by smt.
        - move => Hx1 Hx2. 
          move: H7.
          have ->: oget uL0{2}.[idL <- Flabel idL].[id0] = oget uL0{2}.[id0] by smt.  
          rewrite (H0 id0 _); first by smt.
          have ->: oget uL0{2}.[idL <- Flabel idL].[id'] = Flabel id' by smt.  
          by smt.
    + by smt. 
  inline IPKE(Pe, Ve, HRO.RO).kgen.
  auto; call(_: true).
  call (_: true ==> ={glob HRO.RO}).
    by sim.
  by auto; progress; smt.
qed.

(* bound on the scorr in bpriv by ind1cca *)
lemma scorr_bpriv (LR<: LorR { BS, BP, BIND, BIND2, BSCorr, BSC, 
                                     HRO.RO, A, Ve, C, Vz, Pz, Pe, S, G}) &m:
  Pr[SCorr (HeliosHomWeed(Pe, Ve, Pz, Vz, C), 
            BSCorr(HeliosHomWeed(Pe, Ve, Pz, Vz, C),A, LR), 
            HRO.RO, S).main() @ &m: BSC.valid] = 
`|Pr[Ind1CCA(IPKE(Pe,Ve),
             INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, C), 
                       BSCorr(MV(IPKE(Pe,Ve), Pz,Vz,C),A, LR), S, HRO.RO)),
             HRO.RO,Left).main() @ &m: res /\  size BS.encL <= 1] -
  Pr[Ind1CCA(IPKE(Pe,Ve),
             INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz,C),
                       BSCorr(MV(IPKE(Pe,Ve), Pz, Vz, C),A, LR), S, HRO.RO)),
             HRO.RO,Right).main() @ &m: res /\  size BS.encL <= 1]|. 
proof. 
  rewrite (scorr_HeliosHomWeed_HeliosHom LR &m).

  (* use result from HeliosHom *)
  by rewrite (scorr_bpriv C Pe Ve Pz Vz Rz G S A AC2 AC3 v_distinct Gi_ll Go_ll 
                Si_ll So_ll Sp_ll C_ll Pp_ll Vv_ll Pe_ll Ve_ll A1_ll A2_ll AC2_ll 
                AC_ll Vval_ll Vvot_ll san_tallymap san_mem Verify_to_verify 
                LPKE_prover_keepstate Prover_to_verify Prover_to_verify_left
                validInd_ax enc_to_validInd relConstraint LR &m). 
qed.

local lemma bpriv_equiv &m:
  `|Pr[BPRIV_L(HeliosHomWeed(Pe, Ve, Pz, Vz, C), A, HRO.RO, G).main() @ &m : res] -
    Pr[BPRIV_R(HeliosHomWeed(Pe, Ve, Pz, Vz, C), A, HRO.RO, G, S).main() @ &m :res]| =
  `|Pr[BPRIV_L(HeliosHom(Pe, Ve, Pz, Vz, C), A, HRO.RO, G).main() @ &m : res] -
    Pr[BPRIV_R(HeliosHom(Pe, Ve, Pz, Vz, C), A, HRO.RO, G, S).main() @ &m :res]|.
proof.
  have ->: Pr[BPRIV_L(HeliosHomWeed(Pe, Ve, Pz, Vz, C), 
                      A, HRO.RO, G).main() @ &m : res] =
           Pr[BPRIV_L(HeliosHom(Pe, Ve, Pz, Vz, C), 
                      A, HRO.RO, G).main() @ &m : res].
    byequiv=>//=. 
    proc.
    sim.
    call (_: ={glob HRO.RO, glob G, glob Pz, glob Pe, glob Ve, glob C, 
             BP.bb1, BP.bb0, BP.sk, BP.uL, BP.pk, 
             BP.qVo, BP.qCa }/\
           (forall b, mem BP.bb0{2} b => 
                      oget BP.uL{2}.[b.`1] = b.`2 /\
                      BP.uL{2}.[b.`1] <> None) /\
           (forall (id id': ident), 
                  (BP.uL{2}.[id] <> None /\ BP.uL{2}.[id'] <> None) =>
                      oget BP.uL{2}.[id] = oget BP.uL{2}.[id'] => 
                                  id = id')).
      + proc.
        if =>//=. 
        sp; if; auto.
        seq 6 6 : (={id, v0, v1, glob HRO.RO, glob G, glob Pz,  
                 glob Ve, glob Pe, glob C, BP.bb1, BP.bb0, BP.sk, BP.uL, 
                 BP.pk, BP.qVo, BP.qCa} /\
               (forall b2, mem BP.bb0{2} b2 => 
                           oget BP.uL{2}.[b2.`1] = b2.`2/\
                           BP.uL{2}.[b2.`1] <> None) /\
               (forall (id0 id' : ident),
                    (BP.uL{2}.[id0] <> None /\ BP.uL{2}.[id'] <> None) =>
                      oget BP.uL{2}.[id0] = oget BP.uL{2}.[id'] => 
                      id0 = id')/\
               ={ b0, b1, b, bb} /\ b0{2}.`1 = id{2}/\
               bb{2}=BP.bb0{2}/\ b{2} = b0{2}).
          inline *.
          wp; call(_: ={glob HRO.RO}); first by sim.
          auto; call(_: ={glob HRO.RO}); first by sim.
          by auto. 

       exists* bb{2}, BP.uL{2}, b{2}, BP.pk{2}; elim* => bbx uLx bx pkx.
       call (valid_less2 Left G bbx uLx bx pkx).
       by auto; progress; smt.

      + proc. 
        if; auto.   
        inline LeftOrRight.Left.l_or_r; sp.
        exists* bb{2}, BP.uL{2}, b{2}, BP.pk{2}; elim* => bbx uLx bx pkx.
        call (valid_less2 Left G bbx uLx bx pkx).
        by auto; progress; smt.

      + proc; inline*; auto. 
    
      + proc; auto.

      + have Go: equiv [G.o ~ G.o : ={arg, glob G} ==> ={res, glob G}]
        by proc true; first 2 by progress.
        conseq Go=>//=.  

    inline BPRIV_L(HeliosHomWeed(Pe, Ve, Pz, Vz, C), A, HRO.RO, G).V.setup
      BPRIV_L(HeliosHom(Pe, Ve, Pz, Vz, C), A, HRO.RO, G).V.setup.
    wp; while (={ i, nr, uL} /\ 
         (forall (id id': ident), 
                 (uL{2}.[id] <> None /\ uL{2}.[id'] <> None) =>
                 oget uL{2}.[id] = oget uL{2}.[id'] => id = id')/\
         (forall idx, uL{2}.[idx] <> None => 
                            oget uL{2}.[idx] = Flabel idx)).
      auto; progress. 
      + case (idL = id0).
        + case (idL = id'). 
          + by smt. 
          - move => Hx1 Hx2. 
            move: H7. 
            have ->: oget uL{2}.[idL <- Flabel idL].[id'] = oget uL{2}.[id'] by smt.  
            rewrite (H0 id' _); first by smt.  
            have ->: oget uL{2}.[idL <- Flabel idL].[id0] = Flabel id0 by smt.  
            by smt.
        - case (idL <> id').
          + by smt.
          - move => Hx1 Hx2. 
            move: H7.
            have ->: oget uL{2}.[idL <- Flabel idL].[id0] = oget uL{2}.[id0] by smt.  
            rewrite (H0 id0 _); first by smt.
            have ->: oget uL{2}.[idL <- Flabel idL].[id'] = Flabel id' by smt.  
            by smt.
      + by smt. 

    inline IPKE(Pe, Ve, HRO.RO).kgen.
    auto; call(_: true).
    call (_: true ==> ={glob HRO.RO}); first by sim.
    by auto; progress; smt. 

  have ->: Pr[BPRIV_R(HeliosHomWeed(Pe, Ve, Pz, Vz, C), 
                      A, HRO.RO, G, S).main() @ &m : res] =
           Pr[BPRIV_R(HeliosHom(Pe, Ve, Pz, Vz, C), 
                      A, HRO.RO, G, S).main() @ &m : res].
    byequiv =>//=. 
    proc.
    sim.           
    call (_: ={glob HRO.RO, glob S, glob G, glob Pz, glob Pe, glob Ve, glob C, 
             BP.bb1, BP.bb0, BP.sk, BP.uL, BP.pk, 
             BP.qVo, BP.qCa }/\
           (forall b, mem BP.bb1{2} b => 
                      oget BP.uL{2}.[b.`1] = b.`2 /\
                      BP.uL{2}.[b.`1] <> None) /\
           (forall (id id': ident), 
                  (BP.uL{2}.[id] <> None /\ BP.uL{2}.[id'] <> None) =>
                      oget BP.uL{2}.[id] = oget BP.uL{2}.[id'] => 
                                  id = id')).
      + proc.
        if =>//=. 
        sp; if; auto.
        seq 6 6 : (={id, v0, v1, glob HRO.RO, glob G, glob Pz, glob S,  
                 glob Ve, glob Pe, glob C, BP.bb1, BP.bb0, BP.sk, BP.uL, 
                 BP.pk, BP.qVo, BP.qCa} /\
               (forall b2, mem BP.bb1{2} b2 => 
                           oget BP.uL{2}.[b2.`1] = b2.`2/\
                           BP.uL{2}.[b2.`1] <> None) /\
               (forall (id0 id' : ident),
                    (BP.uL{2}.[id0] <> None /\ BP.uL{2}.[id'] <> None) =>
                      oget BP.uL{2}.[id0] = oget BP.uL{2}.[id'] => 
                      id0 = id')/\
               ={ b0, b1, b, bb} /\ b0{2}.`1 = id{2}/\
               bb{2}=BP.bb1{2}/\ b{2} = b1{2}).
          inline *.
          wp; call(_: ={glob HRO.RO}); first by sim.
          auto; call(_: ={glob HRO.RO}); first by sim. 
          by auto. 

       exists* bb{2}, BP.uL{2}, b{2}, BP.pk{2}; elim* => bbx uLx bx pkx.
       call (valid_less2 Left S bbx uLx bx pkx).
       by auto; progress; smt.

      + proc. 
        if; auto.   
        inline LeftOrRight.Right.l_or_r; sp.
        exists* bb{2}, BP.uL{2}, b{2}, BP.pk{2}; elim* => bbx uLx bx pkx.
        call (valid_less2 Left S bbx uLx bx pkx).
        by auto; progress; smt.

      + proc; inline*; auto. 
    
      + proc; auto.

      + have So: equiv [S.o ~ S.o : ={arg, glob S} ==> ={res, glob S}]
        by proc true; first 2 by progress.
        conseq So=>//=.  

    inline BPRIV_R(HeliosHomWeed(Pe, Ve, Pz, Vz, C), A, HRO.RO, G, S).V.setup
         BPRIV_R(HeliosHom(Pe, Ve, Pz, Vz, C), A, HRO.RO, G, S).V.setup.
    wp; while (={ i, nr, uL} /\ 
         (forall (id id': ident), 
                 (uL{2}.[id] <> None /\ uL{2}.[id'] <> None) =>
                 oget uL{2}.[id] = oget uL{2}.[id'] => id = id')/\
         (forall idx, uL{2}.[idx] <> None => 
                            oget uL{2}.[idx] = Flabel idx)).
      auto; progress. 
      + case (idL = id0).
        + case (idL = id'). 
          + by smt. 
          - move => Hx1 Hx2. 
            move: H7. 
            have ->: oget uL{2}.[idL <- Flabel idL].[id'] = oget uL{2}.[id'] by smt.  
            rewrite (H0 id' _); first by smt.  
            have ->: oget uL{2}.[idL <- Flabel idL].[id0] = Flabel id0 by smt.  
            by smt.
        - case (idL <> id').
          + by smt.
          - move => Hx1 Hx2. 
            move: H7.
            have ->: oget uL{2}.[idL <- Flabel idL].[id0] = oget uL{2}.[id0] by smt.  
            rewrite (H0 id0 _); first by smt.
            have ->: oget uL{2}.[idL <- Flabel idL].[id'] = Flabel id' by smt.  
            by smt.
      + by smt.  

    inline IPKE(Pe, Ve, HRO.RO).kgen.
    auto; call(_: true); call(_: true).
    call (_: true ==> ={glob HRO.RO}); first by sim.
    by auto; progress; smt. 

  by done.
qed.

(* Lemma bounding BPRIV *)
lemma bpriv &m: 
   `|Pr[BPRIV_L(HeliosHomWeed(Pe, Ve, Pz, Vz, C), A, HRO.RO, G).main() @ &m : res] -
     Pr[BPRIV_R(HeliosHomWeed(Pe, Ve, Pz, Vz, C), A, HRO.RO, G, S).main() @ &m :res]|
<=
    Pr[VFR(IPKE(Pe, Ve), BVFR(MV(IPKE(Pe, Ve), Pz, Vz, C), A), 
           Rz(IPKE(Pe,Ve)), HRO.RO, G).main() @ &m : res] +
    Pr[VFR(IPKE(Pe, Ve), BVFR(MV(IPKE(Pe, Ve), Pz, Vz, C), A), 
           Rz(IPKE(Pe,Ve)), HRO.RO, S).main() @ &m : res] +
 `|Pr[ZK_L(Rz(IPKE(Pe, Ve), HRO.RO),
           Pz, BZK(IPKE(Pe, Ve), Pz, C, Vz, A, HRO.RO), G).main() @ &m : res] -
   Pr[ZK_R(Rz(IPKE(Pe, Ve), HRO.RO),
           S , BZK(IPKE(Pe, Ve), Pz, C, Vz, A, HRO.RO)).main() @ &m : res]| +
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
                           BSCorr(MV(IPKE(Pe,Ve),Pz,Vz,C),A, Right), S, HRO.RO)),
                 HRO.RO,Right).main() @ &m: res /\  size BS.encL <= 1]| +
n%r *
   `|Pr[Ind1CCA(IPKE(Pe, Ve), 
                WrapAdv(BIND(MV(IPKE(Pe, Ve), Pz, Vz, C), A, S),IPKE(Pe, Ve), HRO.RO),
                HRO.RO, Left).main() @ &m : res /\ WrapAdv.l <= n /\ size BS.encL <= 1] -
     Pr[Ind1CCA(IPKE(Pe, Ve), 
                WrapAdv(BIND(MV(IPKE(Pe, Ve), Pz, Vz, C), A, S),IPKE(Pe, Ve), HRO.RO), 
                HRO.RO, Right).main()@ &m : res /\ WrapAdv.l <= n /\ size BS.encL <= 1]|.
proof.
  rewrite (bpriv_equiv &m).
  (* bpriv bound for HeliosAbstract *)
  cut oldbpriv:= (bpriv C Pe Ve Pz Vz Rz G S A AC2 AC3 v_distinct Gi_ll Go_ll 
                Si_ll So_ll Sp_ll C_ll Pp_ll Vv_ll Pe_ll Ve_ll A1_ll A2_ll AC2_ll 
                AC_ll Vval_ll Vvot_ll san_tallymap san_mem Verify_to_verify 
                LPKE_prover_keepstate Prover_to_verify Prover_to_verify_left
                validInd_ax enc_to_validInd relConstraint &m). 

  (* make the scorr equal to ind1cca *)
  move: oldbpriv.
  have ->: Pr[SCorr(MV(IPKE(Pe, Ve), Pz, Vz, C), 
                    BSCorr(MV(IPKE(Pe, Ve), Pz, Vz, C), A, Left), 
                    HRO.RO, S).main() @ &m : BSC.valid] = 
           Pr[SCorr (HeliosHom(Pe, Ve, Pz, Vz, C), 
                    BSCorr(HeliosHom(Pe, Ve, Pz, Vz, C),A, Left), 
                    HRO.RO, S).main() @ &m: BSC.valid].
    by byequiv =>//=; sim. (* move this to HeliosHom *)
  rewrite -(scorr_HeliosHomWeed_HeliosHom Left &m).
  rewrite (scorr_bpriv Left &m).
  have ->: Pr[SCorr(MV(IPKE(Pe, Ve), Pz, Vz, C), 
              BSCorr(MV(IPKE(Pe, Ve), Pz, Vz, C), A, Right), 
              HRO.RO, S).main() @ &m : BSC.valid] = 
           Pr[SCorr (HeliosHom(Pe, Ve, Pz, Vz, C), 
              BSCorr(HeliosHom(Pe, Ve, Pz, Vz, C),A, Right), 
              HRO.RO, S).main() @ &m: BSC.valid].
    by byequiv =>//=; sim. (* move this to HeliosHom *)
  rewrite -(scorr_HeliosHomWeed_HeliosHom Right &m).
  by rewrite (scorr_bpriv Right &m).
qed.

(* STRONG CONSITENCY *) 
lemma consis1(id: ident, v: plain, l: label) &m: 
   Pr[SConsis1(HeliosHomWeed(Pe, Ve, Pz, Vz, C), 
               CE(IPKE(Pe,Ve)), HRO.RO, G).main(id,v, l) @ &m: res]  >=
   Pr[PKEvf.Correctness(IPKE(Pe,Ve), HRO.RO).main(v,l) @ &m: res].
proof.
  have ->: Pr[SConsis1(HeliosHomWeed(Pe, Ve, Pz, Vz, C), 
                       CE(IPKE(Pe,Ve)), HRO.RO, G).main(id,v, l) @ &m: res] =
           Pr[SConsis1(HeliosHom(Pe, Ve, Pz, Vz, C), 
                       CE(IPKE(Pe,Ve)), HRO.RO, G).main(id,v, l) @ &m: res].
    by byequiv =>//=; sim.

  by rewrite (consis1 C Pe Ve Pz Vz Rz G S A AC2 AC3 v_distinct Gi_ll Go_ll 
                Si_ll So_ll Sp_ll C_ll Pp_ll Vv_ll Pe_ll Ve_ll A1_ll A2_ll AC2_ll 
                AC_ll Vval_ll Vvot_ll san_tallymap san_mem Verify_to_verify 
                LPKE_prover_keepstate Prover_to_verify Prover_to_verify_left
                validInd_ax enc_to_validInd relConstraint id v l &m). 
qed.

lemma consis2 &m:
  Pr[SConsis2(HeliosHomWeed(Pe, Ve, Pz, Vz, C), 
              C, AC2, HRO.RO, G).main() @ &m: res] = 1%r.
proof. 
  (* we can not reduce HeliosHomWeed to HeliosHom, as the 2 valid alg 
     produce the same output if the label and ident for any ballot from the 
     ballot box satisfy Flabel(id) = label. But, this check is not done by 
     this experiment. 
     This proof based on the proof for sconsis2 in MiniVotingSecurity *)
  byphoare=>//.
  proc.
  inline SConsis2(HeliosHomWeed(Pe, Ve, Pz, Vz, C), 
                  C, AC2, HRO.RO, G).V.valid.
  seq 14: (b0 = b/\ pk = BP.pk)=>//.
    auto.
    progress. 
    call{1} ( AC2_ll (<: SConsis2(HeliosHomWeed(Pe, Ve, Pz, Vz, C), 
                                  C, AC2, HRO.RO, G).O) _ _).
    + by apply HRO.RO_o_ll. 
    + by apply Go_ll.
    inline SConsis2(HeliosHomWeed(Pe, Ve, Pz, Vz, C), 
                    C, AC2, HRO.RO, G).V.setup.
    wp; while{1} (0 <= i <= nr)
             (nr - i); progress.
      by auto; progress; smt.
    inline IPKE(Pe, Ve, HRO.RO).kgen.
    auto; call{1} Gi_ll. 
    call{1} (HRO.RO_init_ll is_finite_h_in distr_h_out). 
    by auto; progress; smt. 
   
    
    exists* (glob C), BP.pk, b; elim* =>gc pk bv. 
    call{1} (validInd_ax gc pk bv); wp.
    call{1} (validInd_ax gc pk bv). 
    by auto; progress; smt.

  hoare; progress. 
  wp.
  call(_: true).
  + by conseq HRO.RO_o_ll. 
  + by conseq Go_ll.
  inline SConsis2(HeliosHomWeed(Pe, Ve, Pz, Vz, C), 
                  C, AC2, HRO.RO, G).V.setup
         IPKE(Pe, Ve, HRO.RO).kgen.
  wp; while(true).
    by auto.
  by auto; call(_: true).
qed.

equiv consis3 &m:
    SConsis3_L(HeliosHomWeed(Pe, Ve, Pz, Vz, C), 
               C, AC3, HRO.RO, G).main ~ 
    SConsis3_R(HeliosHomWeed(Pe, Ve, Pz, Vz, C), 
               CE(IPKE(Pe,Ve)), C, AC3, HRO.RO, G).main
    : ={glob HRO.RO, glob G, glob IPKE(Pe,Ve), 
        glob C, glob Pz, glob AC3} ==> ={res}.
proof.
  transitivity SConsis3_L(HeliosHom(Pe, Ve, Pz, Vz, C), 
                          C, AC3, HRO.RO, G).main 
  (={glob HRO.RO, glob G, glob IPKE(Pe,Ve), glob C, glob Pz, glob AC3} ==> 
   ={res})
  (={glob HRO.RO, glob G, glob IPKE(Pe,Ve), glob C, glob Pz, glob AC3} ==> 
   ={res})=>//=. 

  + by progress; smt.
  + proc; sim. 
  
  transitivity SConsis3_R(HeliosHom(Pe, Ve, Pz, Vz, C), 
                          CE(IPKE(Pe,Ve)), C, AC3, HRO.RO, G).main 
  (={glob HRO.RO, glob G, glob IPKE(Pe,Ve), glob C, glob Pz, glob AC3} ==> 
   ={res})
  (={glob HRO.RO, glob G, glob IPKE(Pe,Ve), glob C, glob Pz, glob AC3} ==> 
   ={res})=>//=. 

  + by progress; smt.

  + conseq (_: ={glob HRO.RO, glob G, glob IPKE(Pe, Ve), 
                 glob C, glob Pz, glob AC3} ==> _)=>//=. 
    by rewrite (consis3 C Pe Ve Pz Vz Rz G S A AC2 AC3 v_distinct Gi_ll Go_ll 
                Si_ll So_ll Sp_ll C_ll Pp_ll Vv_ll Pe_ll Ve_ll A1_ll A2_ll AC2_ll 
                AC_ll Vval_ll Vvot_ll san_tallymap san_mem Verify_to_verify 
                LPKE_prover_keepstate Prover_to_verify Prover_to_verify_left
                validInd_ax enc_to_validInd relConstraint &m). 

  by sim. 
qed.

(* Lemma bounding STRONG CORRECTNESS *)
lemma scorr_bound (AS <: SCorr_Adv' { IPKE(Pe,Ve), Pz, Vz, C, HRO.RO, BSC, BS, G}) &m:
  Pr[SCorr(HeliosHomWeed(Pe, Ve, Pz, Vz, C), 
              AS(HeliosHomWeed(Pe, Ve, Pz, Vz, C)), HRO.RO, G).main() @ &m: BSC.valid] <= 
`|Pr[Ind1CCA(IPKE(Pe,Ve), 
             INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, C), 
                       AS(MV(IPKE(Pe,Ve), Pz, Vz, C)), G, HRO.RO)), 
             HRO.RO,Left).main()  @ &m: res /\  size BS.encL <= 1] -
  Pr[Ind1CCA(IPKE(Pe,Ve), 
             INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, C), 
                       AS(MV(IPKE(Pe,Ve), Pz, Vz, C)), G, HRO.RO)),
             HRO.RO,Right).main()  @ &m: res /\  size BS.encL <= 1]|.
proof.  
  have ->: Pr[SCorr(HeliosHomWeed(Pe, Ve, Pz, Vz, C), 
                    AS(HeliosHomWeed(Pe, Ve, Pz, Vz, C)), 
                    HRO.RO, G).main() @ &m: BSC.valid] =
           Pr[SCorr(MV'(IPKE(Pe, Ve), Pz, Vz, C), 
                    AS(MV'(IPKE(Pe, Ve), Pz, Vz, C)), 
                    HRO.RO, G).main() @ &m: BSC.valid].
    by byequiv =>//=; sim.

  by rewrite (scorr_bound_mv' C Pz Vz G HRO.RO S A Ve Pe Finj v_distinct enc_to_validInd
                     validInd_ax  Prover_to_verify_left  Prover_to_verify Verify_to_verify
                     Pe_ll Ve_ll So_ll Si_ll AC_ll AS G &m Gi_ll Go_ll). 
qed.

end section Security.