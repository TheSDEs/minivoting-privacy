require import FMap List Int FSet Real LeftOrRight Option Fun ExtEq.
require (*  *) MiniVoting_VFR.
require (*  *) Ex_Plug_and_Pray.
 
clone include MiniVoting_VFR. 

section Weeding.
declare module C: ValidInd        {BS, BP, BSC, BSCorr, HRO.RO}. 
declare module E: Scheme          {C, BS, BP, BSC, BSCorr, HRO.RO}.
declare module Pz: Prover         {C, E, BS, BP, BSCorr, HRO.RO}.
declare module Vz: Verifier       {C, E, Pz, BS, BP, BSCorr, HRO.RO}.
declare module G : GOracle.Oracle {C, E, Pz, Vz, BP}.
declare module H : HOracle.Oracle {C, E, Pz, Vz, G, BP}.
declare module S : Simulator      {C, E, Pz, Vz, G, H, BSC, BSCorr, BP, BS, HRO.RO}.
declare module A : BPRIV_Adv      {C, E, Pz, Vz, G, H, S, BSC, BS, BSCorr, BP, HRO.RO}. 

(* ** ASSUMPTIONS ** *)
(* ** start *)
  (* axiom for injectivity over label *)
  axiom F_inj(x y: ident): 
    Flabel x = Flabel y => x = y.
(* ** end *)

(* Helios' voting system *) 
module MV' (E : Scheme, Pz: Prover,  
            Vz: Verifier,   C : ValidInd,
            H : HOracle.ARO,G : GOracle.ARO)={

  proc setup  = MV(E, Pz, Vz, C, H, G).setup
  proc vote   = MV(E, Pz, Vz, C, H, G).vote
  proc tally  = MV(E, Pz, Vz, C, H, G).tally
  proc verify = MV(E, Pz, Vz, C, H, G).verify

  (* validation algorithm *)
  proc valid (bb: (ident * label * cipher) list, 
              uL: (ident, label) map, 
              b: (ident * label * cipher),
              pk: pkey): bool = {
    var ev1, ev2, ev3;

    ev2 <- false;
    ev3 <- true;

    (* membership check for entire ballot  *)
    ev1 <- mem bb b ;
    (* check id and label from ballot *)
    if( uL.[b.`1] <> None){
      ev2 <- (oget uL.[b.`1]) = b.`2;
    }
 
    (*  validInd *)
    ev3 <@ C(H).validInd(b,pk);

    return (!ev1 /\ ev2 /\ ev3);
  }
}.

(* Lemma show that MV.valid and MV'.valid are the same, 
   if the label is injective *)
equiv same_valid (Gx<: GOracle.ARO {H, C})
                       (bbx: (ident * label * cipher) list)
                       (uLx: (ident, label) map) 
                       (bx: ident * label * cipher) 
                       (pkx: pkey):
  MV(E, Pz, Vz, C, H, Gx).valid ~ MV'(E, Pz, Vz, C, H, Gx).valid
  : ={glob H, glob C, arg} /\ arg{2} = (bbx, uLx, bx, pkx) /\
    (forall b, mem bbx b => oget uLx.[b.`1] = b.`2/\
                            uLx.[b.`1] <> None) /\
    (forall (id id': ident), 
            (uLx.[id] <> None /\ uLx.[id'] <> None) =>
            oget uLx.[id] = oget uLx.[id'] => id = id')
      ==>
    ={res, glob H, glob C}/\
     (res{2} =>  uLx.[bx.`1] <> None /\
                 oget uLx.[bx.`1] = bx.`2).
proof.
  proc.
  call (_: ={glob H}).
    by sim.
  wp; while{1} (0 <= i{1} <= size bb{1} /\
            (!ev1{1} <=> forall id, 
                         !mem (take i{1} bb{1}) (id, b{1}.`2, b{1}.`3)))
           (size bb{1} - i{1}); progress.
  auto; progress.
  + smt. 
  + smt. 
  + have Hm: 0<= i{hr} < size bb{hr} by done.
    rewrite (take_nth witness) 1: Hm //; rewrite mem_rcons in_cons. 
    by smt.
  + have Hm: 0<= i{hr} < size bb{hr} by done.
    move : H4; rewrite (take_nth witness) 1: Hm //. 
    move => Hid.    
    cut := Hid (nth witness bb{hr} i{hr}).`1. 
    by smt.
  + by smt.
  + by smt.
  + by smt.
  + have Hm: 0<= i{hr} < size bb{hr} by done.
    cut Hx: exists id, mem (take i{hr} bb{hr}) (id, b{hr}.`2, b{hr}.`3) by smt.
    move:Hx; elim => id Hx.  
    rewrite nforall //=; rewrite (take_nth witness) 1: Hm //. 
    exists id. 
    by smt.
  + by smt.

  auto; progress.
  + by smt. + by smt. + by smt.
  + move: H4; have ->: (take i_L bb{2}) = bb{2} by smt.
    move => H4. 
    case (oget uL{2}.[b{2}.`1] = b{2}.`2). 
    + move => Hc.
      rewrite H4 eq_iff //=.
      progress.
      + by move : (H6 b{2}.`1); case (b{2}).

      have Hx: ! mem bb{2} (b{2}.`1, b{2}.`2, b{2}.`3) by smt.
      case (id = b{2}.`1).
      + by smt. 
      - move => Hn. 
        have Hxc:= H0 id b{2}.`1. 
        case (mem bb{2} (id, b{2}.`2, b{2}.`3)). 
        + move => Hxd.
          cut Hd:= H (id, b{2}.`2, b{2}.`3) Hxd.
          have Hg: uL{2}.[id] = Some b{2}.`2 by smt. 
          cut Hcc:= Hxc _; first by smt.
          by smt. 
        - by smt.
    - by smt.
qed.

(* case study: bpriv with MV' *)
local lemma noWeeding_left &m:
  Pr[BPRIV_L(MV (E, Pz, Vz, C), A, H, G).main() @ &m : res] =
  Pr[BPRIV_L(MV'(E, Pz, Vz, C), A, H, G).main() @ &m : res].
proof.
  byequiv (_: ={glob A, glob E, glob Pz, glob Vz, 
                glob C, glob G, glob H} ==> _)=>//=.
  proc.
  (* A.a2 call *)
  call (_: ={glob H, glob G, glob Pz, glob Vz, glob E, glob C, 
             BP.bb1, BP.bb0, BP.sk, BP.uL, BP.pk});
      [1..3: by sim]. 
  call(_: ={glob H, glob G, glob Pz, glob E}).
    by sim.
  (* A.a1 call *)
  call (_: ={glob H, glob G, glob Pz, glob Vz, glob E, glob C, 
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
    seq 6 6 : (={id, v0, v1, glob H, glob G, glob Pz, glob Vz, 
                 glob E, glob C, BP.bb1, BP.bb0, BP.sk, BP.uL, 
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
      wp; call(_: ={glob H}). 
        by sim.
      wp; call(_: ={glob H}).
        by sim.
      by auto. 

     exists* bb{2}, BP.uL{2}, b{2}, BP.pk{2}; elim* => bbx uLx bx pkx.
     call (same_valid G bbx uLx bx pkx).
     by auto; progress; smt.
     
  + proc. 
    if; auto.   
    inline LeftOrRight.Left.l_or_r; sp.
    exists* bb{2}, BP.uL{2}, b{2}, BP.pk{2}; elim* => bbx uLx bx pkx.
    call (same_valid G bbx uLx bx pkx).
    by auto; progress; smt.

  + proc; inline*; auto. 
    
  + have Ho: equiv [H.o ~ H.o : ={arg, glob H} ==> ={res, glob H}]
      by proc true; first 2 by progress.
    conseq Ho=>//=.
  + have Go: equiv [G.o ~ G.o : ={arg, glob G} ==> ={res, glob G}]
      by proc true; first 2 by progress.
    conseq Go=>//=.   

  inline BPRIV_L(MV (E, Pz, Vz, C), A, H, G).V.setup
         BPRIV_L(MV'(E, Pz, Vz, C), A, H, G).V.setup.
  wp.  
  while (={ i, nr, uL} /\ 
         (forall (id id': ident), 
                 (uL{2}.[id] <> None /\ uL{2}.[id'] <> None) =>
                 oget uL{2}.[id] = oget uL{2}.[id'] => id = id')/\
         (forall idx, uL{2}.[idx] <> None => 
                            oget uL{2}.[idx] = Flabel idx)).
    auto; progress. 
    + cut Ht := H id0 id'.
      case (idL <> id0 /\ idL <> id'). 
      + by smt.
      - rewrite -nand //=.
        move => Hx. 
        case (idL = id0). 
        + case (idL = id').
          + by smt.
          - move => Hc1 Hc2.
            move: H7.
            have ->: oget uL{2}.[idL <- Flabel idL].[id0] = Flabel id0 by smt.
            have ->: oget uL{2}.[idL <- Flabel idL].[id'] = oget uL{2}.[id'] by smt.
            by smt.
       - move => Hc1. 
         by smt.
    + by smt.

  call(_: ={glob H}).
  wp; call(_: true); call(_: true).
  by auto; progress; smt.
qed.

local lemma noWeeding_right &m:
  Pr[BPRIV_R(MV (E, Pz, Vz, C), A, H, G, S).main() @ &m : res] =
  Pr[BPRIV_R(MV'(E, Pz, Vz, C), A, H, G, S).main() @ &m : res].
proof.
  byequiv (_: ={glob A, glob E, glob Pz, glob S,
                glob Vz, glob C, glob G, glob H} ==> _)=>//=.
  proc.
  (* A.a2 call *)
  call (_: ={glob H, glob G, glob Pz, glob Vz, glob E, glob S, 
             glob C, BP.bb1, BP.bb0, BP.sk, BP.uL, BP.pk});
      [1..3: by sim].
  call (_: true). 
  wp; call(_: ={glob H, glob G, glob Pz, glob E}).
    by sim.
  (* A.a1 call *)
  call (_: ={glob H, glob G, glob Pz, glob Vz, glob E, glob S, glob C, 
             BP.bb1, BP.bb0, BP.sk, BP.uL, BP.pk, BP.qVo, BP.qCa}/\
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
    seq 6 6 : (={id, v0, v1, glob H, glob G, glob Pz, glob Vz, glob S,
                 glob E, glob C, BP.bb1, BP.bb0, BP.qVo, BP.qCa, BP.sk, 
                 BP.uL, BP.pk} /\
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
      wp; call(_: ={glob H}). 
        by sim.
      wp; call(_: ={glob H}).
        by sim. 
      by auto. 

     exists* bb{2}, BP.uL{2}, b{2}, BP.pk{2}; elim* => bbx uLx bx pkx.
     call (same_valid S bbx uLx bx pkx).
     by auto; progress; smt.
     
  + proc. 
    if; auto.   
    inline LeftOrRight.Right.l_or_r; sp.
    exists* bb{2}, BP.uL{2}, b{2}, BP.pk{2}; elim* => bbx uLx bx pkx.
    call (same_valid S bbx uLx bx pkx).
    by auto; progress; smt.

  + proc; inline*; auto.

  + have Ho: equiv [H.o ~ H.o : ={arg, glob H} ==> ={res, glob H}]
      by proc true; first 2 by progress.
    conseq Ho=>//=.
  + have So: equiv [S.o ~ S.o : ={arg, glob S} ==> ={res, glob S}]
      by proc true; first 2 by progress.
    conseq So=>//=.

  inline BPRIV_R(MV (E, Pz, Vz, C), A, H, G, S).V.setup
         BPRIV_R(MV'(E, Pz, Vz, C), A, H, G, S).V.setup.
  wp.
  while (={ i, nr, uL} /\ 
         (forall (id id': ident), 
                 (uL{2}.[id] <> None /\ uL{2}.[id'] <> None) =>
                 oget uL{2}.[id] = oget uL{2}.[id'] => id = id')/\
         (forall idx, uL{2}.[idx] <> None => 
                            oget uL{2}.[idx] = Flabel idx)).
    auto; progress. 
    + cut Ht:= H id0 id'.
      case (idL <> id0 /\ idL <> id'). 
      + by smt.
      - rewrite -nand //=. 
        case (idL = id0). 
        + case (idL = id').
          + by smt.
          - move => Hc1 Hc2. 
            move: H7.
            have ->: oget uL{2}.[idL <- Flabel idL].[id0] = Flabel id0 by smt.
            have ->: oget uL{2}.[idL <- Flabel idL].[id'] = oget uL{2}.[id'] by smt.
            by smt.
        - move => Hc1. 
          by smt.
    + by smt.
  call(_: ={glob H}).
  wp; call(_: true); call(_: true); call(_: true).
  by auto; progress; smt.
qed.
end section Weeding.

section Weeding_Strong_Correctness.

declare module C: ValidInd        {BS, BP, BSC, BSCorr, HRO.RO}. 
declare module E: Scheme          {C, BS, BP, BSC, BSCorr, HRO.RO}.
declare module Pz: Prover         {C, E, BS, BP, BSCorr, HRO.RO}.
declare module Vz: Verifier       {C, E, Pz, BS, BP, BSCorr, HRO.RO}.
declare module G : GOracle.Oracle {C, E, Pz, Vz, BP}.
declare module H : HOracle.Oracle {C, E, Pz, Vz, G, BP}.
declare module S : Simulator      {C, E, Pz, Vz, G, H, BSC, BSCorr, BP, BS, HRO.RO}.
declare module A : BPRIV_Adv      {C, E, Pz, Vz, G, H, S, BSC, BS, BSCorr, BP, HRO.RO}. 

(* ** ASSUMPTIONS ** *)
(* ** start *)
  (* at least 2 distinct votes *)
  axiom v_distinct: v_def_0 <> v_def_1.

  (* encryption always implies validInd true *)
  axiom enc_to_validInd (pk: pkey) (id: ident) (v: vote) (l : label):
    equiv[E(HRO.RO).enc ~ E(HRO.RO).enc: 
          ={glob HRO.RO, glob E, arg} /\ arg{1} = (pk,l,v)
         ==> ={res, glob E, glob HRO.RO} /\
          validInd pk (id, l, res{1}) HRO.RO.m{1}].

  (* axiom for linking C.validInd to validInd operator  *)
  axiom validInd_ax (gc: (glob C)) (pk: pkey) (b: ident * label * cipher):
    phoare [C(HRO.RO).validInd: 
            (glob C) = gc /\ arg = (b, pk) 
            ==>
            (glob C) = gc /\ res = validInd pk b HRO.RO.m] = 1%r.
  
   
  (* axiom for transforming an encryption into decryption (one-sided) *)
  axiom Eenc_decL (ge: (glob E)) (sk2: skey) 
                 (pk2: pkey)(l2: label) (p2: vote): 
    (pk2 = extractPk sk2) =>
    phoare [E(HRO.RO).enc : (glob E) = ge /\ arg=( pk2, l2, p2)
          ==> 
          (glob E) = ge /\ 
          Some p2 = dec_cipher sk2 l2 res HRO.RO.m]= 1%r.

   (* axiom for transforming an encryption into decryption (two-sided) *)
  axiom Eenc_dec (sk2: skey) (pk2: pkey) (l2: label) (p2: vote): 
    (pk2 = extractPk sk2) =>
    equiv [E(HRO.RO).enc ~ E(HRO.RO).enc : 
          ={glob HRO.RO, glob E, arg} /\ arg{1}=( pk2, l2, p2)   
          ==> 
          ={glob HRO.RO, glob E,  res} /\ 
          Some p2 = dec_cipher sk2 l2 res{1} HRO.RO.m{1}].

  (* axiom for linking E.dec to dec_cipher operator *)
  axiom Edec_Odec (ge: (glob E))
                (sk2: skey)(l2: label) (c2: cipher):
    phoare [E(HRO.RO).dec:  (glob E) =ge /\ 
           arg = (sk2, l2, c2) 
           ==>   
           (glob E) =ge /\
           res = dec_cipher sk2 l2 c2 HRO.RO.m ] = 1%r.

  (* axiom for stating that the keys are generated (two-sided) *)
  axiom Ekgen_extractPk (H<: HOracle.ARO):
    equiv [E(H).kgen ~ E(H).kgen:  ={glob H, glob E} ==> 
          ={glob H, glob E,  res} /\ 
          res{1}.`1 = extractPk res{1}.`2  /\
          res{1}.`1 = extractPk res{1}.`2 ].

  (* axiom for stating that the keys are generated (one-sided) *)
  axiom Ekgen_extractPkL (H<: HOracle.ARO):
    phoare [E(H).kgen: true 
           ==>   
           res.`1 = extractPk res.`2 ] = 1%r.

  (* lossless *)
  axiom Ek_ll(H <: HOracle.ARO): 
    islossless H.o =>
    islossless E(H).kgen.
  axiom Ee_ll(H <: HOracle.ARO): 
    islossless H.o =>
    islossless E(H).enc.
  axiom Ed_ll(H <: HOracle.ARO): 
    islossless H.o =>
    islossless E(H).dec.

  axiom So_ll: islossless S.o.
  axiom Si_ll: islossless S.init.

  axiom AC_ll (AS <: SCorr_Adv') 
              (V<: VotingScheme { AS }) (O <: SCorr_Oracle { AS }):
    islossless O.h => 
    islossless O.g => 
    islossless O.test =>
    islossless AS(V,O).main.
(* ** end *)

  
(* Lemma to show reduction from strong correctness experiment to 
          membership check experiment for minivoting'.
   This proof is important as MV' valid ~ MV.valid only under the assumption 
        that all ballots (id,lbl, c) from the ballot box satisfy Flabel(id)=lbl.
        As this check is not performed by the strong correctness experiment, 
        we must reshow this reduction for MiniVoting'. *)
local lemma scorr_to_mem_mv' (AS <: SCorr_Adv' { E, Pz, Vz, C, HRO.RO, BSC} ) 
                  (G <: GOracle.Oracle { BS, BP, BSC, BSCorr, HRO.RO, E, Pz, Vz, C, AS}) &m:
  Pr[SCorr(MV'(E, Pz, Vz, C), 
           AS(MV'(E, Pz, Vz, C)), HRO.RO, G).main() @ &m: BSC.valid ] <=
  Pr[MemCheck(E, HRO.RO, 
              Bmem(MV(E, Pz, Vz, C), AS(MV(E, Pz, Vz, C)), G, HRO.RO)).main() @ &m: BSC.valid].
proof.
  byequiv(_: ={glob AS, glob G, glob E} ==> _ ) =>//=.
  proc.
  inline Bmem(MV(E, Pz, Vz, C), AS(MV(E, Pz, Vz, C)), G, HRO.RO, 
              MemCheck(E, HRO.RO, Bmem(MV(E, Pz, Vz, C), AS(MV(E, Pz, Vz, C)), G, HRO.RO)).MO).main.
  call(_: ={glob HRO.RO, glob G, glob E, BSC.qt, BSC.uL, BSC.pk}/\
          BSC.qt{1} <= 1 /\ (BSC.valid{1} => BSC.valid{2})).
  + by proc; auto.
  + by proc (={glob HRO.RO, glob E, BSC.qt, BSC.uL, BSC.pk} /\ 
             BSC.qt{1} <= 1 /\ (BSC.valid{1} => BSC.valid{2}));
      progress.
  + proc.
    inline Coll_Oracle(E, HRO.RO).mem_test.
    sp.
    seq 0 1: (l{2} = BSC.uL{2}.[id{2}] /\ 
                ={id, v, bb, BSC.qt, BSC.uL,
                  BSC.pk, glob G, glob E, glob HRO.RO} /\
                cL{2} = map (fun (b: ident * label * cipher) 
                              => (b.`3, b.`2)) bb{2} /\
                BSC.qt{1} <= 1 /\ (BSC.valid{1} => BSC.valid{2})).
      while{2} (0 <= i{2} <= size bb{2} /\
                cL{2} = map (fun (b: ident * label * cipher) 
                                => (b.`3, b.`2))
                               (take i{2} bb{2}))
                 (size bb{2} - i{2}); progress.
        auto; progress.       
        + by smt. 
        + by smt.
        + have Hm: 0<= i{hr} < size bb{hr} by done.
          rewrite (take_nth witness) 1: Hm //. 
          by smt.
        + by smt.   
      by auto; progress; smt.
    sp; if =>//=. 
    if =>//=; first by auto; progress; smt.   
      sp; if =>//=; last by auto; progress; smt.  
      inline *.
      seq 15 1: (l{1} = BSC.uL{1}.[id{1}] /\
                 l{2} = BSC.uL{2}.[id{2}] /\
                 l{1} <> None /\
                 l'{1} = oget l{1} /\ 
                 l0{1} = l'{1} /\
                 l0{2} = l{2} /\

                 id0{1} = id{1} /\ 
                 v0{1} = v{1} /\
                 v0{2} = v{2} /\
                 pk{1} = BSC.pk{1} /\
                 pk0{1} = BSC.pk{1}/\
                 cL0{2} = cL{2} /\          
                 ={id, v, bb, BSC.qt, glob E, 
                   BSC.uL, BSC.pk, glob G, HRO.RO.m} /\
                 cL{2} = map (fun (b1 : ident * label * cipher)
                              => (b1.`3, b1.`2)) bb{2} /\
                  BSC.qt{1} <= 1 /\
                  BSC.qt{1} < 1 /\
                  size bb{1} < n + k /\
                  ={c} /\ 
                  b0{1} = (id, l0, c){1} /\
                  b0{1} = b{1} /\ 
                  bb0{1} = bb{1} /\
                  ev2{1} /\
                  validInd pk{1} (id{1}, l0{1}, c{1}) HRO.RO.m{1}/\
                  (BSC.valid{1} => BSC.valid{2})/\
                  ev1{1} = mem bb0{1} (id{1}, l0{1}, c{1})).
        wp; sp.
        exists* BSC.pk{1}, id{1}, v0{1}, l0{1};
          elim* => pk1 id1 v01 l01.
       call{1} (enc_to_validInd pk1 id1 v01 l01). 
       by auto; progress; smt.
       
          
       wp; exists* (glob C){1}, BSC.pk{1}, b{1}; elim* => gc pk1 b1.
       call{1} (validInd_ax gc pk1 b1).
       auto; progress; smt.

    by auto; progress; smt.
    
  inline SCorr(MV'(E, Pz, Vz, C), AS(MV'(E, Pz, Vz, C)), HRO.RO, G).V.setup.
  wp; while (={ i}/\ nr{1} = part /\ uL{1} = BSC.uL{2}).
    by auto.
  swap{1} [5..8] 1.
  wp; call (_: true). 
  wp; call (_: ={glob HRO.RO}). 
  call (_: true ==> ={glob HRO.RO});
    first by sim.
  by auto.
qed.

(* Lemma bounding strong correctness *)
lemma scorr_mv' (AS <: SCorr_Adv' { E, Pz, Vz, C, HRO.RO, BSC, BS}) 
                  (G  <: GOracle.Oracle { BS, BP, BSC, BSCorr, HRO.RO, E, Pz, Vz, C, AS, S, A}) &m:
  islossless G.init =>
  islossless G.o =>
  Pr[SCorr(MV'(E, Pz, Vz, C), 
           AS(MV'(E,Pz,Vz,C)), HRO.RO, G).main() @ &m: BSC.valid ] <= 
`|Pr[Ind1CCA(E,INDB(Bmem(MV(E, Pz, Vz, C), AS(MV(E, Pz, Vz, C)), G, HRO.RO)),
             HRO.RO,Left).main()  @ &m: res /\  size BS.encL <= 1] -
  Pr[Ind1CCA(E,INDB(Bmem(MV(E, Pz, Vz, C), AS(MV(E, Pz, Vz, C)), G, HRO.RO)),
             HRO.RO,Right).main()  @ &m: res /\  size BS.encL <= 1]|.
proof.
  move => Gi_ll Go_ll. 

  rewrite -(mem_to_ind E S Vz Pz C A v_distinct  enc_to_validInd validInd_ax
                    Eenc_decL  Eenc_dec  Edec_Odec  Ekgen_extractPk Ekgen_extractPkL 
                    Ek_ll Ee_ll Ed_ll So_ll Si_ll AC_ll AS G &m).
  rewrite (ind_to_zero E S Vz Pz C A v_distinct  enc_to_validInd validInd_ax
                    Eenc_decL  Eenc_dec  Edec_Odec  Ekgen_extractPk Ekgen_extractPkL 
                    Ek_ll Ee_ll Ed_ll So_ll Si_ll AC_ll AS G &m Gi_ll Go_ll).
  have Hx: forall (a: real), 0%r <= a => `|a-0%r| = a by smt.
  rewrite Hx; first by smt.
  by rewrite (scorr_to_mem_mv' AS G &m).
qed.

end section Weeding_Strong_Correctness.
