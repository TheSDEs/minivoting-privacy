require import Int Bool Real FMap.
require import List Distr Option.
require import Logic Pred Pair.
require import LeftOrRight.
require import DatatypesExt.
require (*  *) MiniVotingDefinition.
require (*  *) Ex_Plug_and_Pray.
require (*  *) ROM.

clone include MiniVotingDefinition. 

(* eager random oracle *)
clone ROM.Eager as HRO with
  type from    <- h_in,
  type to      <- h_out,
  op dsample(inp: h_in) <- dh_out
  proof *.  

(* MiniVoting security concepts:
   + ballot privacy, with main lemma bpriv,
   + strong consistency with the lemmas consis1, consis2, consis3, and
   + strong correctness with the lemma scorr and scorr_bpriv *) 

(* ---------------------------------------------------------------------- *)
(* Ballot Privacy *)
section BPRIV. 

declare module G : GOracle.Oracle 
                   { BP, BS, BPS, BIND, HRO.RO}.
declare module E : Scheme        
                   { BP, BS, BPS, BSC, BIND, HRO.RO, G, BSCorr,  
                     PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv, BPRIV_SB, BIND2}.
declare module S : Simulator 
                   { BP, BS, BPS, BSC, BIND, HRO.RO, G, E, BSCorr,
                     BPRIV_SB, BIND2, PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv}.
declare module Ve: Verifier
                   { BP, BS, BPS, BSC, BSCorr, BIND, HRO.RO, G, E, S}.
declare module P : Prover
                   { BP, BS, BPS, BSC, BSCorr, BIND, HRO.RO, G, E, S, Ve}.
declare module R : VotingRelation' 
                   { BPS, BP, BS, G, E, S, P, Ve, HRO.RO}.
declare module C: ValidInd       
                   { BP, BS, BPS, BSC, BIND, HRO.RO, BSCorr, G, E, S, Ve, P, R, 
                     BPRIV_SB,  BIND2, PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv}.
declare module A: BPRIV_Adv        
                  { BP, BS, BPS, BSC, HRO.RO, G, E, S, Ve, P, R, C, PKEvf.H.Count, 
                    PKEvf.H.HybOrcl, WrapAdv, BSCorr, BPRIV_SB, BIND, BIND2}. 

(* ** ASSUMPTIONS ** *)
(* ** start *)
  (* lossless *)
  (* -> for oracles *)
  axiom Gi_ll: islossless G.init.
  axiom Go_ll: islossless G.o.

  (* -> for BPRIV adversary *)
  axiom Aa1_ll (O <: BPRIV_Oracles { A }):
    islossless O.vote    =>
    islossless O.cast    =>
    islossless O.board   =>
    islossless O.h       =>
    islossless O.g       =>
    islossless A(O).a1.
  axiom Aa2_ll (O <: BPRIV_Oracles { A }):
    islossless O.board =>
    islossless O.h     =>
    islossless O.g     =>
    islossless A(O).a2.

  (* -> for proof system *)
  axiom Pp_ll (G <: GOracle.ARO): 
    islossless G.o =>
    islossless P(G).prove. 
  axiom Vv_ll (G <: GOracle.ARO):
    islossless G.o =>
    islossless Ve(G).verify.

  (* -> for encryption *)
  axiom Ek_ll (H <: HOracle.ARO): 
    islossless H.o =>
    islossless E(H).kgen.
  axiom Ee_ll(H <: HOracle.ARO): 
    islossless H.o =>
    islossless E(H).enc.
  axiom Ed_ll(H <: HOracle.ARO): 
    islossless H.o =>
    islossless E(H).dec.
  
  (* -> for ZK simulator *)
  axiom Si_ll: islossless S.init.
  axiom So_ll: islossless S.o.
  axiom Sp_ll: islossless S.prove.

  (* -> for Strong consistency Op *)
  axiom Co_ll (H <: HOracle.ARO):
    islossless H.o =>
    islossless C(H).validInd.
  
  (* -> for any voting scheme *) 
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

  (* axiom on a voting relation that does not 
     change the state of the eager random oracle *)
  axiom relConstraint (gh : (glob HRO.RO)):
    phoare[ R(E,HRO.RO).main : 
          (glob HRO.RO) = gh ==> (glob HRO.RO) = gh] = 1%r.


  (* axiom for result distribution *)
  axiom Rho_weight (x: (ident * vote option) list):
    weight (Rho x) = 1%r.

  (* decryption operator with access to a map of values, 
     instead of random oracle*)
  op dec_cipher: skey -> label -> cipher  -> 
              (h_in, h_out) map -> vote option.

  (* axiom for stating that the keys are generated *)
  axiom Ekgen_extractPk (H<: HOracle.ARO):
    equiv [E(H).kgen ~ E(H).kgen:  ={glob H, glob E} ==> 
          ={glob H, glob E,  res} /\ 
          res{1}.`1 = extractPk res{1}.`2  /\
          res{1}.`1 = extractPk res{1}.`2 ].

  (* axiom for linking E.dec to dec_cipher operator *)   
  axiom Edec_Odec (ge: (glob E)) (sk2: skey)(l2: label) (c2: cipher):
    phoare [E(HRO.RO).dec:  
           (glob E) =ge /\ arg = (sk2, l2, c2)
           ==>   
           (glob E) =ge /\
           res = dec_cipher sk2 l2 c2 HRO.RO.m ] = 1%r.

  (* axiom on the state of the encryption scheme E *)
  axiom Ee_eq (ge: (glob E)):
    phoare [E(HRO.RO).enc: 
          (glob E) = ge ==> (glob E) = ge] = 1%r.
    
  (* axiom for transforming an encryption into decryption (one-sided) *)
  axiom Eenc_decL (ge: (glob E)) (sk2: skey) 
                  (pk2: pkey)(l2: label) (p2: vote): 
    (pk2 = extractPk sk2) =>
    phoare [E(HRO.RO).enc : 
          (glob E) = ge /\ arg=(pk2, l2, p2) 
          ==> 
          (glob E) = ge /\
          Some p2 = dec_cipher sk2 l2 res HRO.RO.m ]= 1%r.   

  (* axiom for transforming an encryption into decryption (two-sided) *)
  axiom Eenc_dec (sk2: skey) (pk2: pkey) (l2: label) (p2: vote): 
    (pk2 = extractPk sk2) =>
    equiv [E(HRO.RO).enc ~ E(HRO.RO).enc : 
          ={glob HRO.RO, glob E, arg} /\ arg{1}=( pk2, l2, p2) 
          ==> 
          ={glob HRO.RO, glob E,  res} /\
          Some p2 = dec_cipher sk2 l2 res{1} HRO.RO.m{1}].   
(* ** end *)

(* decryption should not change the state of an eager random oracle *) 
local lemma Edec_Odec_eq (sk2: skey)(l2: label) (c2: cipher):
  equiv [E(HRO.RO).dec ~ E(HRO.RO).dec :
          ={glob HRO.RO, glob E, arg}/\ arg{1} = (sk2, l2, c2)
           ==>   
           ={glob HRO.RO, glob E, res} /\
           res{1} = dec_cipher sk2 l2 c2 HRO.RO.m{1} ].
proof.
  proc*=>//=. 
  exists* (glob E){1}; elim* => ge.
  call{1} (Edec_Odec ge sk2 l2 c2 ).
  call{2} (Edec_Odec ge sk2 l2 c2 ). 
  by auto.
qed.

(* the state of the simulated is the same in two-sided call *)
local equiv So_ll2: S.o ~ S.o : ={arg, glob S} ==> ={res, glob S}.
proof. by proc true. qed.  

(* the remove identity operator is a function applied to each ballot*)
local lemma remid_map (xs: (ident * label * cipher) list):
   remID xs = map (fun (b : ident * label * cipher), (b.`3, b.`2)) xs.
proof.
  elim xs =>//.
qed.


(* lemmas for losslessness of BZK.b1 *) 
local lemma b1_ll (H<: HOracle.Oracle { E, A, BP }) 
            (G<: GOracle.ARO { A }):
  islossless H.init =>
  islossless H.o    =>
  islossless G.o    =>
  islossless BZK(E, P, C, Ve, A, H, G).a1.
proof.
  move=> Hi_ll Ho_ll Go_ll.
  proc; auto. 
  while (true) (size BP.bb0 - i).
  + move => z; wp.
    call{1} (Ed_ll H Ho_ll).
    by auto; smt.

  (* A.a1 call *)
  wp; call (Aa1_ll (<: BZK(E,P,C,Ve,A,H,G).O) _ _ _ _ _) =>//.
  + (* O.vote *)
    proc. 
    if =>//. 
    sp; if =>//; last by wp.
    wp; inline *; wp. 
    call (Co_ll H Ho_ll).
    wp; while (true) (size bb - i).
      by auto; smt.
    wp; call (Ee_ll H Ho_ll). 
    wp; call (Ee_ll H Ho_ll).
    by auto; smt.
  + (* O.cast *)
    proc. 
    if =>//=.
    inline *; wp. 
    call (Co_ll H Ho_ll).
    wp; while (true) (size bb0 - i).
      by auto; smt.
    by auto; smt.
  + (* O. board *)
    by proc; inline*; wp.

  while (true) (part - i). 
    by auto; progress; smt. 
  conseq (_: _ ==> true). 
    progress; first 2 by rewrite -lezNgt -subz_le0. 
    by smt. 
  call (Ek_ll H Ho_ll); call Hi_ll. 
  by auto. 
qed.

(* lemmas for losslessness of BZK.b2 *) 
lemma b2_ll  (H <: HOracle.Oracle{ A, BPS })
             (G <: GOracle.ARO{ A, BPS, H }):
  islossless H.o =>
  islossless G.o =>
  islossless BZK(E, P, C, Ve, A, H, G).a2.
proof.
  move=> Ho_ll Go_ll; proc.
  call (Aa2_ll (<:BZK(E,P,C,Ve,A,H,G).O) _ _ _) =>//.
    by proc; inline*; wp. 
qed.

lemma b2'_ll (H<: HOracle.Oracle { A }) 
             (G <: GOracle.ARO{ A, H })
             (P <: Prover { E, C, Ve, A, ZK_L, BPS, BP, H, G }):
  islossless H.o =>
  islossless G.o =>
  islossless P(G).prove =>
  islossless BZK(E, P, C, Ve, A, H, G).a2.
proof.
  move=> Ho_ll Go_ll Pp_ll; proc.
  call (Aa2_ll (<:BZK(E,P,C,Ve,A,H,G).O) _ _ _) =>//.
    by proc; inline*; wp.
qed.

(* left game for ZK without checking the relation *)
local module ZKFL(E: Scheme, R: VotingRelation', P:Prover, 
                  A:VotingAdvZK, 
                  H: HOracle.Oracle, O:GOracle.Oracle) = {

  proc main(): bool = {
    var p;

                      O.init();
    (BPS.s, BPS.w) <@ A(H,O).a1();
    BPS.rel        <@ R(E,H).main(BPS.s, BPS.w);
    p              <@ P(O).prove(BPS.s, BPS.w);
    BPS.p          <- Some p;
    BPS.b          <@ A(H,O).a2(BPS.p);

    return BPS.b;
  }
}.



(* right game for ZK without checking the relation *)
local module ZKFR(E: Scheme, R: VotingRelation', S:Simulator, 
                  A:VotingAdvZK, H: HOracle.Oracle) = {

  proc main(): bool = {
    var p;

                      S.init();
    (BPS.s, BPS.w) <@ A(H,S).a1();
    BPS.rel        <@ R(E, H).main(BPS.s, BPS.w);
    p              <@ S.prove(BPS.s);
    BPS.p          <- Some p;
    BPS.b          <@ A(H,S).a2(BPS.p);

    return BPS.b;
  }
}.



(* Lemma relating ZKFL to interesting non-local modules *)
local lemma ZKFL_ZKL (O <: GOracle.Oracle {BPS}) 
                     (R <: VotingRelation' {BPS, O})
                     (H <: HOracle.Oracle {BPS, BP, BS, R, O})
                     (P <: Prover {BPS, R, H, O}) 
                     (B <: VotingAdvZK {BPS, P, H, R, O}) &m:
  islossless O.o     =>
  islossless P(O).prove =>
  islossless B(H,O).a2 =>
    `|Pr[ZKFL(E, R, P, B, H, O).main() @ &m : res]
    - Pr[ZK_L(R(E,H), P, B(H), O).main() @ &m : res]|
  <=  Pr[ZK_L(R(E,H), P, B(H), O).main() @ &m : !BPS.rel].
proof.
  move=> Oo_ll Pp_ll Ba2_ll.
  byequiv ( _: ={glob B, glob P, glob R, glob H, glob O} ==>
                ={BPS.rel} /\
              (BPS.rel{2} => ={res}))
           : (!BPS.rel)=> //; last smt.
  proc.
  seq 3 3: (={glob B, glob P, glob H, glob O, BPS.s, BPS.w, BPS.rel}). 
    call (_: ={glob H}); first by sim.
    call (_: ={glob H, glob O}); first 3 by sim.
    by call (_: true).
    
  if{2}; first by sim.
  call{1} Ba2_ll.
  call{2} Ba2_ll.
  by wp; call{1} Pp_ll.
qed.

(* Lemma relating ZKFR to interesting non-local modules *)
local lemma ZKFR_ZKR (S <: Simulator {BPS}) 
                     (R <: VotingRelation' {BPS, S})
                     (H <: HOracle.Oracle {BPS, BP, BS, R, S})
                     (B <: VotingAdvZK {BPS, S, R, H}) &m:
  islossless S.o     =>
  islossless S.prove =>
  islossless B(H,S).a2 =>
    `|  Pr[ZKFR(E, R, S, B, H).main() @ &m : res]
      - Pr[ZK_R(R(E, H), S, B(H)).main() @ &m : res]|
     <= Pr[ZK_R(R(E, H), S, B(H)).main() @ &m : !BPS.rel].
proof.
  move=>  So_ll Sp_ll Ba2_ll.
  byequiv ( _: ={glob B, glob S, glob R, glob H} ==>
               ={BPS.rel} /\
              (BPS.rel{2} => ={res}))
           : (!BPS.rel)=> //; last smt.
  proc.
  seq 3 3: (={glob B, glob S, glob H, BPS.s, BPS.w, BPS.rel}). 
    call (_: ={glob H}); first by sim.
    call (_: ={glob H, glob S}); first 3 by sim.
    by call (_: true).

  if{2}; first by sim.
  call{1} Ba2_ll.
  call{2} Ba2_ll.
  by wp; call{1} Sp_ll; auto.
qed.

(* Lemma bounding ZKL with relation that does not hold by VFZK Rel *)
local lemma ZKL_Rel (H <: HOracle.Oracle {A, BPS, BP, BS, Ve, E, C, R})
                    (G <: GOracle.Oracle {A, BPS, BP, BS, Ve, E, H, R, C}) 
                    (P <: Prover {E, C, Ve, A, R, BPS, BP, BS, H, G}) &m:
  islossless H.o        => 
  islossless G.o        =>
  islossless P(G).prove =>
    Pr[ZK_L(R(E,H), P, BZK(E,P,C,Ve,A,H), G).main() @ &m: !BPS.rel ] 
 <= Pr[VFR(E, BVFR(MV(E,P,Ve,C), A), R(E), H, G).main() @ &m: res].
proof.
  move=> Ho_ll Go_ll Pop_ll.
  byequiv (_ : ={glob A, glob E, glob P, glob Ve, glob C, 
                 glob H, glob G, glob R} ==> _)=> //.
  proc.
  call{1} (b2'_ll H G P Ho_ll Go_ll Pop_ll).
  inline *.

  (* remove the if-else on {1} to obtain indistinguish games *)
  seq 18 21 :( BPS.rel{1} = rel{2} ). 
  call (_: ={glob H}); first by sim.
  auto; while (={glob E, glob A, glob Ve, glob H, ubb, i} /\
         BP.sk{1} = BS.sk{2} /\ BP.bb0{1}= bb{2}).
    by sim.
  swap{2} 1 16.
  wp.

  (* A.a1 call *)
  call (_: ={glob E, glob H, glob G, glob C, glob P, 
             BP.pk, BP.uL, BP.bb0, BP.bb1, 
             BP.qVo, BP.qCa} );
    [1..5: by sim].  
  while ( = {BP.uL} /\ i{1} = i0{2}).
    by sim.
  swap{1} 1 8; wp.
  call( _: ={glob H}).
  call( _: true).
  call( _: true). 
  by auto.

  wp; if{1}; last by auto.
  wp; call{1} Pop_ll.
  by auto.
qed.

(* Lemma bounding ZKFL-ZKL by VFZK Rel *)
local lemma ZKFL_Rel(H <: HOracle.Oracle {A, BPS, BP, BS, Ve, E, C, R})
                    (G <: GOracle.Oracle {A, BPS, BP, BS, Ve, E, H, C, R}) 
                    (P <: Prover { BPS, BP, BS, E, C, Ve, A, G, H, R}) &m:
  islossless H.o =>
  islossless G.o =>
  islossless P(G).prove =>
    `|Pr[ZKFL(E,R, P, BZK(E,P,C,Ve,A), H, G).main() @ &m : res ] -
      Pr[ZK_L(R(E,H), P, BZK(E,P,C,Ve,A,H), G).main() @ &m : res ]| <=
      Pr[VFR (E, BVFR(MV(E,P,Ve,C),A), R(E), H, G).main() @ &m: res].
proof.
  move=> Ho_ll Go_ll Pp_ll. 
  cut L1:= ZKFL_ZKL G R H P (BZK(E,P,C, Ve, A)) &m Go_ll Pp_ll 
                          (b2'_ll H G P Ho_ll Go_ll Pp_ll). 
  cut L2:= ZKL_Rel H G P  &m Ho_ll Go_ll Pp_ll. 
  by smt. 
qed.

(* Lemma for equivalence of BPRIVL and ZKFL *)
local lemma eq_MV_ZKFL &m (H <: HOracle.Oracle { BP, BS, BPS, BIND, PKEvf.H.Count, 
                                   PKEvf.H.HybOrcl, WrapAdv, G, E, S, Ve, P, C, A}):
  islossless H.o =>
  (forall (gh: (glob H)), 
           phoare [R(E,H).main: (glob H) = gh ==> (glob H) = gh ] = 1%r) => 
    Pr[BPRIV_L(MV(E,P,Ve,C), A, H, G).main() @ &m : res ] = 
    Pr[ZKFL(E, R, P, BZK(E,P,C,Ve, A), H, G).main() @ &m : res ].
proof.
  move => Ho RH.
  byequiv (_: ={glob A , glob P, glob H,
                glob G, glob E, glob C } ==> _) => //.
  proc.
  inline *; wp.
  seq 22 17: (={ glob H, glob G, glob P, glob A, BP.bb0, BP.bb1, ubb}/\
              BPS.s{2} = (pk0, pbb, r){1} /\
              BPS.w{2} = (sk0, bb){1} /\
              r{1} = BP.r{2}).
    auto; while (={glob A, glob E, glob H, glob G, ubb} /\
         i0{1} = i{2}      /\
         bb{1} = BP.bb0{2} /\
         sk0{1} = BP.sk{2} ).
      by sim.

    swap{2} 7 6; wp.
    conseq (_ : _ ==> ={glob A, glob H, glob G, glob E, 
                      glob P, BP.bb0, BP.bb1, BP.sk, 
                      BP.pk, BP.qVo, BP.qCa}/\
                    extractPk BP.sk{1} = BP.pk{2} ); first by done. 
    call (_ : ={glob P, glob E, glob H, glob G, glob C, 
              BP.bb0, BP.bb1, BP.pk, BP.uL, 
              BP.qVo, BP.qCa});
      [1..5: by sim].

    wp; while ( ={i}/\ nr{1} = part/\ uL{1} = BP.uL{2}).
      by auto.
    call (Ekgen_extractPk H).
    auto; swap{2} 1 7.
    call (_: true); call (_: true).
    by auto; progress; smt.

  call ( _ : ={ glob H, glob G, BP.bb0, BP.bb1}); 
    [1..3:by sim].
  wp.
  conseq (_: _ ==> (={glob A, glob H, glob G, BP.bb0, BP.bb1}) /\
                     pi{1} = p{2}/\ r{1} = BP.r{2})=>//=.
  call (_: ={ glob G}). 
    by sim.
  exists* (glob H){2}; elim*=> gh.
  call{2} (RH gh).
  by auto.
qed.

(* Lemma bounding ZKFL-ZKL by VFR *)
local lemma bound_ZKFL_Rel &m (H <: HOracle.Oracle { BP, BS, BPS, BIND, PKEvf.H.Count, 
                                       PKEvf.H.HybOrcl, WrapAdv, G, E, S, Ve, P, C, A, R}):
    islossless H.o =>
    `|Pr[ZKFL(E, R, P, BZK(E,P,C,Ve, A), H, G).main() @ &m : res] -
      Pr[ZK_L(R(E, H), P, BZK(E,P,C,Ve, A, H), G).main() @ &m : res]| <=
      Pr[VFR (E, BVFR(MV(E,P,Ve,C),A), R(E), H, G).main() @ &m: res].
proof. 
  by move=> Ho_ll; apply (ZKFL_Rel H G P &m Ho_ll Go_ll (Pp_ll G Go_ll)). 
qed.

local lemma eq_MV'_ZKFR &m (H <: HOracle.Oracle { BP, BS, BPS, BIND, PKEvf.H.Count, 
                                    PKEvf.H.HybOrcl, WrapAdv, G, E, S, Ve, P, C, A}):
  (forall (gh: (glob H)), phoare [R(E, H).main: (glob H) = gh ==> (glob H) = gh ] = 1%r)=>
    Pr[IBPRIV(MV(E,P,Ve,C), A, H, G, S).main() @ &m : res] =
    Pr[ZKFR(E, R, S, BZK(E,P,C,Ve,A), H).main() @ &m : res].
proof.
  move => RH.
  byequiv (_: ={glob A, glob P, glob H, glob S, 
                glob E, glob C} ==> _) => //.
  proc.
  inline*; wp.
  seq 23 17: (={ glob H, glob S, glob P, glob A, BP.bb0, BP.bb1, ubb}/\
              BPS.s{2} = (pk0, pbb0, r){1} /\
              BPS.w{2} = (sk0, bb){1} /\
              r{1} = BP.r{2} /\
              BP.pk{1} = pk0{1} /\
              Publish BP.bb0{2} = pbb0{1}).
    auto; while (={glob A, glob E, glob H, glob S, ubb} /\
         i0{1} = i{2}      /\
         bb{1} = BP.bb0{2} /\
         sk0{1} = BP.sk{2} ).
      by sim.

    swap{2} 7 6; wp.
    conseq (_ : _ ==> ={glob A, glob H, glob S, glob E, 
                      glob P, BP.bb0, BP.bb1, BP.sk, 
                      BP.pk, BP.qVo, BP.qCa}/\
                    extractPk BP.sk{1} = BP.pk{2} ); first done. 
    call (_ : ={glob P, glob E, glob H, glob S, glob C, 
              BP.bb0, BP.bb1, BP.pk, BP.uL, 
              BP.qVo, BP.qCa});
      [1..5: by sim].

    wp; while ( ={i}/\ nr{1} = part/\ uL{1} = BP.uL{2}).
      by auto.
    call (Ekgen_extractPk H).
    auto; swap{2} 1 7.
    call (_: true); call{1} Gi_ll; call (_: true).
    by auto; progress; smt.

  call ( _ : ={ glob H, glob S, BP.bb0, BP.bb1});
    [1..3:by sim].
  wp.
  conseq (_: _ ==> ={glob A, glob H, glob S, BP.r, 
                     BP.bb0, BP.bb1} /\ pi{1} = p{2})=> //=. 
  call (_: true).
  wp; call{1} (Pp_ll G Go_ll).
  exists* (glob H){2}; elim* => gh.
  by call{2} (RH gh).
qed. 

(* Lemma bounding ZKR with Relation that does not hold by VFR *)
local lemma ZKR_Rel (H<: HOracle.Oracle{A, BPS, BP, BS, Ve, E, C, R})
                    (S<: Simulator {A, BPS, BP, BS, Ve, E, H, C, R})  &m:
  islossless H.o     => 
  islossless S.o     =>
  islossless S.prove =>
    Pr[ZK_R(R(E, H), S, BZK(E,P,C,Ve,A,H)).main() @ &m: !BPS.rel ] 
 <= Pr[VFR(E, BVFR(MV(E,P,Ve,C), A), R(E), H, S).main() @ &m: res].
proof.
  move=> Ho_ll So_ll Sp_ll.
  byequiv (_ : ={glob A, glob E, glob S, glob Ve, 
                 glob C, glob H, glob R} ==> _)=> //.
  proc.
  call{1} (b2_ll H S Ho_ll So_ll).
  inline *.

  (* remove the if-else on {1} to obtain indistinguish games *)
  seq 18 21 :( BPS.rel{1} = rel{2}). 
    call (_: ={glob H}); first by sim.
    auto; while (={glob E, glob A, glob Ve, glob H, ubb, i} /\
               BP.sk{1} = BS.sk{2} /\ BP.bb0{1}= bb{2}).
      by sim.
    swap{2} 1 16; wp.
    conseq (_: _ ==> 
             ={glob E, glob A, glob H, glob Ve, ubb, BP.bb0, BP.qVo, BP.qCa} /\
               BP.sk{1} = BS.sk{2} /\ BP.pk{1} = BS.pk{2})=> //=.  
    call (_: ={glob E, glob H, glob S, glob C,
             BP.pk, BP.uL, BP.bb0, BP.bb1, 
             BP.qVo, BP.qCa} );
      [1..5: by sim].  
    while (={BP.uL} /\ i{1} = i0{2}).
      by sim.
    swap{1} 1 8; wp.
    call( _: ={glob H}).
    call( _: true); call( _: true). 
    by auto.

  wp; if{1}; last by auto.
  wp; call{1} Sp_ll.
  by auto.
qed.

(* Lemma bounding ZKFR-ZKR by VFR *) 
local lemma bound_ZKFR_Rel &m (H <: HOracle.Oracle { BP, BS, BPS, BIND, PKEvf.H.Count, 
                                       PKEvf.H.HybOrcl, WrapAdv, G, E, S, Ve, P, C, A, R}):
   islossless H.o =>
    `|Pr[ZKFR(E, R, S, BZK(E,P,C,Ve, A),H).main() @ &m : res] -
      Pr[ZK_R(R(E,H), S, BZK(E,P,C,Ve,A, H)).main() @ &m : res]|
   <= Pr[VFR (E, BVFR(MV(E,P,Ve,C), A), R(E), H, S).main() @ &m: res].
proof. 
  move=> Ho_ll. 
  cut R1:= ZKFR_ZKR S R H (BZK(E,P,C,Ve,A)) &m 
            So_ll Sp_ll (b2_ll H S Ho_ll So_ll).
  cut R2:= ZKR_Rel H S &m Ho_ll So_ll Sp_ll.
  by smt. 
qed.

(* Lemma bounding |BPRIV-L -IBPRIV| by 2* VFR and |ZKL-ZKR| *)
local lemma bound_MV_MV' &m (H <: HOracle.Oracle { BP, BS, BPS, BIND, PKEvf.H.Count, 
                               PKEvf.H.HybOrcl, WrapAdv, G, E, S, Ve, P, C, A, R}):
   islossless H.o =>
   (forall (gh : (glob H)),
    phoare[ R(E,H).main : (glob H) = gh ==> (glob H) = gh] = 1%r)=>
    `|Pr[BPRIV_L(MV(E,P,Ve,C), A, H, G   ).main() @ &m : res ] -
      Pr[IBPRIV(MV(E,P,Ve,C), A, H, G, S).main() @ &m : res]|
   <= Pr[VFR (E, BVFR(MV(E,P,Ve,C), A), R(E), H, G).main() @ &m: res] +
      Pr[VFR (E, BVFR(MV(E,P,Ve,C), A), R(E), H, S).main() @ &m: res] +
    `|Pr[ZK_L(R(E,H), P, BZK(E,P,C,Ve,A,H), G).main() @ &m : res] -
      Pr[ZK_R(R(E,H), S, BZK(E,P,C,Ve,A,H)   ).main() @ &m : res]|.
proof.
  move=> Ho RH.
  cut trig: forall (x y z w: real), `|x - y| <= 
                                    `|x - z| +`|z - w |+ `|y - w| by smt.
  rewrite (eq_MV_ZKFL &m H Ho RH). 
  rewrite (eq_MV'_ZKFR &m H RH).
  cut I2ZKI3:= trig (Pr[ZKFL(E, R, P, BZK(E,P,C,Ve,A), H, G).main() @ &m : res])
                    (Pr[ZKFR(E, R, S, BZK(E,P,C,Ve,A), H    ).main() @ &m : res])
                    (Pr[ZK_L(R(E,H), P, BZK(E,P,C,Ve,A,H), G).main() @ &m : res])
                    (Pr[ZK_R(R(E,H), S, BZK(E,P,C,Ve,A,H)).main() @ &m : res]).
  cut L:= bound_ZKFL_Rel &m H Ho.
  cut R:= bound_ZKFR_Rel &m H Ho.
  by smt.
qed.

(* Lemma equivalence IBPRIV to BPRIV with single board *)
local lemma left_to_sgBoard2 &m:
   Pr[IBPRIV   (MV(E,P,Ve,C), A, HRO.RO, G, S).main() @ &m : 
                  res] =
   Pr[BPRIV_SB (E, C, A, HRO.RO, Left, S).main() @ &m : 
                  res]. 
proof.
  byequiv (_: ={glob E, glob A, glob S, glob C} ==> _) =>//.
  proc.
  swap{2} 3 10.
  swap{2} 6 7.
  seq 10 11: ( ={glob E, glob A, glob S, glob C, glob HRO.RO, 
                 BP.uL, BP.pk, BP.qVo, BP.sk, BP.qCa}/\
               BP.qVo{2} <= n /\  
               BP.bb0{1} = BPRIV_SB.bb{2} /\
               (BP.pk{1} = extractPk BP.sk{1}) /\
               (forall (l,c), mem BPRIV_SB.encL{2} (c, l) => 
                    BPRIV_SB.hvo{2}.[(c,l)] 
                    = dec_cipher BP.sk{2} l c HRO.RO.m{2}) /\
               (forall (id, id',c,l), mem BPRIV_SB.bb{2} (id,l,c)=>
                  mem BPRIV_SB.bb{2} (id',l,c) => id = id'))=>//=.
    (* A.a1 call *)
    wp; call (_: ={glob E, glob S, glob C, glob HRO.RO, BP.uL, BP.pk, 
                   BP.qVo, BP.sk, BP.qCa}/\
                BP.qVo{2} <= n /\  
                BP.bb0{1} = BPRIV_SB.bb{2} /\
                (BP.pk{1} = extractPk BP.sk{1}) /\
                (forall (l,c), mem BPRIV_SB.encL{2} (c, l) => 
                  BPRIV_SB.hvo{2}.[(c,l)] 
                  = dec_cipher BP.sk{2} l c HRO.RO.m{2}) /\
                (forall (id, id',c,l), mem BPRIV_SB.bb{2} (id,l,c)=>
                  mem BPRIV_SB.bb{2} (id',l,c) => id = id')).
         
    (* A.a1: vote oracle *)
    + proc. 
      if =>//=; sp.
      if; auto; last by progress; smt.
      inline Left.l_or_r; wp.
      seq 2 4: (={glob E, glob S, glob C, glob HRO.RO, BP.uL, 
                BP.pk, BP.sk, BP.qVo, BP.qCa, l, id, v0, v1} /\
              BP.qVo{2} < n  /\
              BP.bb0{1}=BPRIV_SB.bb{2}  /\
              b0{1}  = b{2}              /\
              BP.uL{1}.[id{1}] <> None   /\
              (BP.pk{1} = extractPk BP.sk{1})  /\
              Some v0{1} <> None         /\
              b{2}.`1 = id{2}            /\
              Some v0{1} = 
                dec_cipher BP.sk{1} b0{1}.`2 b0{1}.`3 HRO.RO.m{1}/\
              (forall (l,c), mem BPRIV_SB.encL{2} (c, l) => 
                BPRIV_SB.hvo{2}.[(c,l)]  
                 = dec_cipher BP.sk{2} l c HRO.RO.m{2})/\
              (forall (id, id',c,l), mem BPRIV_SB.bb{2} (id,l,c)=>
               mem BPRIV_SB.bb{2} (id',l,c) => id = id')).            

      + inline *; wp; sp.
        exists *  BP.sk{1}, BP.pk{1}, l{1}, v{1}; 
        elim * => sk1 pk1 l1 p1.
        pose kp:= (pk1 = extractPk sk1).
        cut em_kp: kp \/ !kp by smt. 
        elim em_kp. 
   
        + move => h.
          call{1}( Eenc_dec sk1 pk1 l1 p1 h ).  
          by auto; progress; smt. 
        - move => h.
          conseq(_: _ ==> !(BP.pk{1}= extractPk BP.sk{1}))=>//=.
          call{1} (Ee_ll HRO.RO HRO.RO_o_ll).  
          call{2} (Ee_ll HRO.RO HRO.RO_o_ll).  
          by auto; progress; smt. 

      seq 1 0: (={glob E, glob S, glob C, glob HRO.RO, BP.uL, 
                BP.pk, BP.sk, BP.qVo, BP.qCa, l, id, v0, v1} /\
              BP.qVo{2} < n               /\
              BP.bb0{1}=BPRIV_SB.bb{2}  /\
              b0{1}  = b{2}              /\
              BP.uL{1}.[id{1}] <> None   /\
              (BP.pk{1} = extractPk BP.sk{1})  /\
              Some v0{1} <> None         /\
              b{2}.`1 = id{2}            /\
              Some v0{1} = 
                dec_cipher BP.sk{1} b0{1}.`2 b0{1}.`3 HRO.RO.m{2} /\
              (forall (l,c), mem BPRIV_SB.encL{2} (c, l) => 
                BPRIV_SB.hvo{2}.[(c,l)] 
                = dec_cipher BP.sk{2} l c HRO.RO.m{2})/\
              (forall (id, id',c,l), mem BPRIV_SB.bb{2} (id,l,c)=>
               mem BPRIV_SB.bb{2} (id',l,c) => id = id')).
  
      + inline *; wp; sp. 
        exists* (glob E){1}; elim* => ge.
        call{1} (Ee_eq ge).  
        by auto; progress; smt. 

      sp. 
      (* Valid is true, if for (b{2}.`2,b{2}.`3) there exists no id, such that 
               (id, b{2}.`2, b{2}.`3) is in bb{2} *)

      exists* b{2}; elim* =>b2.
      call (_: ={glob C, glob HRO.RO, BP.uL, BP.pk, arg} /\
             BP.bb0{1} = BPRIV_SB.bb{2} /\
             arg{2}.`1 = BPRIV_SB.bb{2} /\
             arg{2}.`3 = b2 ==>
             ={glob HRO.RO, glob C, BP.uL, BP.pk, res } /\
             BP.bb0{1} = BPRIV_SB.bb{2} /\
             (res{2} => forall id, ! mem BPRIV_SB.bb{2} (id, b2.`2, b2.`3))).
      + proc.
        wp; call (_: ={glob HRO.RO}); first by sim.
        wp; while (={ i, bb, ev1, b} /\ 0<=i{2}  /\
                 (!ev1{2} => forall id, 
                             !mem (take i{2} bb{2}) (id, b{2}.`2, b{2}.`3))).         
          auto; progress. 
          + by smt. 
          + rewrite take_onth; first by done. 
            rewrite mem_rcons in_cons -nor (H0 H3 id) //=.
            by smt.
          + by smt.
        by auto; progress; smt. 
        (* end Valid *)

      auto; progress.
      + by smt. 
      + case (mem BPRIV_SB.encL{2} (c, l0)).
        + rewrite cats1 mem_rcons in_cons in H6.
          by smt.
        - move => Hm.  
          have Hx: (b{2}.`3, b{2}.`2) = (c, l0) by smt.
          by smt. 
       + case (mem BPRIV_SB.bb{2} (id0, l0, c)).
         + case (mem BPRIV_SB.bb{2} (id', l0, c)).
           + by smt.
           - move => Hm Hn. 
             rewrite mem_cat mem_seq1 in H6.
             rewrite mem_cat mem_seq1 in H7.
             have Ho: b{2} = (id', l0, c) by smt.
             by smt.
         - move => Hm.
           rewrite mem_cat mem_seq1 in H6.
           rewrite mem_cat mem_seq1 in H7.
           have Ho: b{2} = (id0, l0, c) by smt.
           by smt.
       + smt.
     
    (* A.a1: cast oracle *)
    + proc. 
      if; auto.

      (* Valid gives true for any id, (id,b{2}.`2,b{2}.`3) not in bb{2} *)
      exists* b{2}; elim* =>b2.
      call (_: ={glob HRO.RO, glob C, BP.uL, BP.pk, arg} /\
             BP.bb0{1} = BPRIV_SB.bb{2} /\
             arg{2}.`1 = BPRIV_SB.bb{2} /\
             arg{2}.`3 = b2 ==>
             ={glob HRO.RO, glob C, BP.uL, BP.pk, res } /\
             BP.bb0{1} = BPRIV_SB.bb{2} /\
             (res{2} => forall id, ! mem BPRIV_SB.bb{2} (id,b2.`2,b2.`3))).
      + proc.
        call (_: ={glob HRO.RO}); first by sim.
        wp;while (={ i, bb, ev1, b} /\ 0<= i{2} /\
                  (!ev1{2} => forall id, 
                            !mem (take i{2} bb{2}) (id, b{2}.`2, b{2}.`3))). 
          auto; progress. 
          + by smt.
          + rewrite take_onth; first by done.
            rewrite mem_rcons in_cons -nor (H0 H3 id).
            by smt.
          + by smt.
        by auto; progress; smt.
        (* end Valid *)
     
      inline *; auto; progress.   
      + case (mem BPRIV_SB.bb{2} (id, l, c)).
        + case (mem BPRIV_SB.bb{2} (id', l, c)).
          + by progress; rewrite (H1 id id' c l).  
          - move => Hm Hn.  
            rewrite mem_cat mem_seq1 in H5.
            rewrite mem_cat mem_seq1 in H6.
            have Ho: b{2} = (id', l, c) by smt.
            by smt.
        - move => Hm.
          rewrite mem_cat mem_seq1 in H5.
          rewrite mem_cat mem_seq1 in H6.
          have Ho: b{2} = (id, l, c) by smt.
          by smt.
     
    (* A.a1: board, H, S oracle *)
    by proc; inline *; auto.
    by proc; auto; progress; smt.    
    by conseq So_ll2; progress.

    (* before A.a1 call *)
    inline MV(E, P, Ve, C, HRO.RO, G).setup
    BPRIV_SB(E, C, A, HRO.RO, Left, S).MV.setup.
    wp; while (={uL}/\ nr{1}= n{2} /\ i{1} = i0{2}).
      by auto.
    call{1} (Ekgen_extractPk HRO.RO).
    wp; call(_: true).
    call{1} Gi_ll.
    call (_: true ==> ={glob HRO.RO}).
      by sim.
    by auto; progress; smt.

  (* A.a2 call *)
  call (_: ={glob E, glob HRO.RO, glob S, glob C, 
             BP.pk,  BP.sk, BP.sk, BP.qVo} /\
             BP.bb0{1}=BPRIV_SB.bb{2}). 
  + by proc; inline *; auto. 
  + by sim.
  + by sim.
  conseq (_: ={BP.r, pi, glob A, glob E, glob S, glob C, 
               glob HRO.RO, BP.pk, BP.sk, BP.qVo}/\
             BP.bb0{1} = BPRIV_SB.bb{2} )=>//=. 
  wp; call(_: true).
  inline MV(E, P, Ve, C, HRO.RO, G).tally.
  inline *; wp.

  (* tally phase *)
  wp; call{1} (Pp_ll G Go_ll).
  auto; while (={i, ubb, glob E, glob HRO.RO}    /\ 
           bb{1} = BPRIV_SB.bb{2} /\
           BP.sk{2} = sk{1}       /\ 
           0 <= i{1}              /\
           (forall (l,c), mem BPRIV_SB.encL{2} (c, l) => 
              BPRIV_SB.hvo{2}.[(c,l)]  
               = dec_cipher BP.sk{2} l c HRO.RO.m{2})/\
           (forall (id, id',c,l), mem BPRIV_SB.bb{2} (id,l,c)=>
              mem BPRIV_SB.bb{2} (id',l,c) => id = id')).
    + wp; sp.
      exists* (glob E){1}, sk{1}, b{1}; elim * => ge sk1 b1. 
      if{2}.
      + call (Edec_Odec_eq sk1 b1.`2 b1.`3).     
        by auto; progress; smt. 
      - call{1} (Edec_Odec ge sk1 b1.`2 b1.`3 ). 
        by auto; progress; smt.

  by auto. 
qed.

(* Lemma equivalence BPRIVR to BPRIV with single board *)
lemma right_to_sgBoard2 &m:
   Pr[BPRIV_R (MV(E,P,Ve,C), A, HRO.RO, G, S).main() @ &m : res ] =
   Pr[BPRIV_SB (E, C, A, HRO.RO, Right, S).main() @ &m :  res ]. 
proof.
  byequiv (_: ={glob E, glob A, glob S, glob C} ==> _) =>//.
  proc. 
  (* A.a2 call *)
  call (_: ={glob E, glob S, glob C, glob HRO.RO,
             BP.pk,  BP.sk, BP.sk, BP.qVo} /\
             BP.bb1{1}=BPRIV_SB.bb{2}).
  + by proc; inline *; auto. 
  + by sim.
  + by sim.
  wp; call(_: true).
  inline BPRIV_R(MV(E, P, Ve, C), A, HRO.RO, G, S).V.tally.
  wp; call{1} (Pp_ll G Go_ll).
 
  (* tally phase *)
  auto; while (={i, ubb, glob E, glob HRO.RO, BP.sk}    /\ 
             0 <= i{1} /\
             BP.sk{2} = sk{1} /\  
             BP.bb0{1} = bb{1} /\
             size BPRIV_SB.bb{2} = size bb{1}  /\
             (forall i, 0 <= i < size BPRIV_SB.bb{2} =>
                (nth witness BPRIV_SB.bb{2} i).`1 =  
                (nth witness BP.bb0{1} i).`1) /\ 
             (forall i, let b = nth witness BP.bb0{1} i in 
                        let b'= nth witness BPRIV_SB.bb{2} i in
                0 <= i < size BP.bb0{1} /\ 
                mem BPRIV_SB.encL{2} (b'.`3, b'.`2) =>
                  BPRIV_SB.hvo{2}.[(b'.`3, b'.`2)]  
                  = dec_cipher BP.sk{1} b.`2 b.`3 HRO.RO.m{1} )/\
             (forall i, let b = nth witness BP.bb0{1} i in 
                        let b'= nth witness BPRIV_SB.bb{2} i in
                0 <= i < size BP.bb0{1} /\ 
                BPRIV_SB.hvo{2}.[(b'.`3, b'.`2)] = None =>
                  b = b')/\
             (forall (c,l), mem BPRIV_SB.encL{2} (c,l) =>
                exists id, mem BPRIV_SB.bb{2} (id,l,c))/\
             (forall (l,c), ! mem BPRIV_SB.encL{2} (c,l) =>
                BPRIV_SB.hvo{2}.[(c,l)]  = None)/\
             (forall (id, id',c,l), mem BPRIV_SB.bb{2} (id,l,c)=>
                mem BPRIV_SB.bb{2} (id',l,c) => id = id')).

    + wp; sp.
      exists* (glob E){1}, sk{1}, b{1}; elim * => ge sk1 b1. 
      if{2}.    
      + call{1} (Edec_Odec_eq sk1 b1.`2 b1.`3).
        by auto; progress; smt.  
      - call{1} (Edec_Odec ge sk1 b1.`2 b1.`3).
        by auto; progress; smt.
              
  (* A.a1 call *)
  wp; call (_: ={glob E, glob S, glob C, glob HRO.RO,
                 BP.uL, BP.pk, BP.qVo, BP.qCa, BP.sk} /\
               BP.qVo{2} <= n /\
               BP.bb1{1}=BPRIV_SB.bb{2}               /\
               size BPRIV_SB.bb{2} = size BP.bb0{1}  /\
               (BP.pk{1} =extractPk BP.sk{1})         /\
               (forall i, 0 <= i < size BPRIV_SB.bb{2} =>
                  (nth witness BPRIV_SB.bb{2} i).`1 =  
                  (nth witness BP.bb0{1} i).`1) /\ 
               (forall i, let b = nth witness BP.bb0{1} i in 
                          let b'= nth witness BPRIV_SB.bb{2} i in
                  0 <= i < size BP.bb0{1} /\ 
                  mem BPRIV_SB.encL{2} (b'.`3, b'.`2) =>
                    BPRIV_SB.hvo{2}.[(b'.`3, b'.`2)]  
                    = dec_cipher BP.sk{1} b.`2 b.`3 HRO.RO.m{1})/\
               (forall i, let b = nth witness BP.bb0{1} i in 
                          let b'= nth witness BPRIV_SB.bb{2} i in
                  0 <= i < size BP.bb0{1} /\ 
                  BPRIV_SB.hvo{2}.[(b'.`3, b'.`2)] = None =>
                    b = b')/\
               (forall (c,l), mem BPRIV_SB.encL{2} (c,l) =>
                  exists id, mem BPRIV_SB.bb{2} (id,l,c))/\
               (forall (l,c), ! mem BPRIV_SB.encL{2} (c,l) =>
                  BPRIV_SB.hvo{2}.[(c,l)]  = None)/\
               (forall (id, id',c,l), mem BPRIV_SB.bb{2} (id,l,c)=>
                  mem BPRIV_SB.bb{2} (id',l,c) => id = id')).       
                      
    (* A.a1: vote oracle *)
    + proc. 
      if =>//=; sp.
      if; auto; last by progress; smt.
      inline Right.l_or_r; wp.
      seq 6 4: (={glob E, glob S, glob C, glob HRO.RO, BP.uL, 
                BP.pk, BP.sk, BP.qVo, BP.qCa, id, v0, v1,b} /\
              BP.qVo{2} < n /\
              b0{1}.`1 = b1{1}.`1  /\ 
              b1{1}  = b{2} /\
              bb{1} = BPRIV_SB.bb{2} /\ 
              BP.bb1{1} = BPRIV_SB.bb{2} /\
              size BPRIV_SB.bb{2} = size BP.bb0{1} /\ 
              (BP.pk{1} =extractPk BP.sk{1})       /\
              (forall i, 0 <= i < size BPRIV_SB.bb{2} =>
                (nth witness BPRIV_SB.bb{2} i).`1 =  
                (nth witness BP.bb0{1} i).`1) /\ 
              (forall i, let b = nth witness BP.bb0{1} i in 
                         let b'= nth witness BPRIV_SB.bb{2} i in
                0 <= i < size BP.bb0{1} /\ 
                mem BPRIV_SB.encL{2} (b'.`3, b'.`2) =>
                   BPRIV_SB.hvo{2}.[(b'.`3, b'.`2)]  
                   = dec_cipher BP.sk{1} b.`2 b.`3  HRO.RO.m{1})/\
              (forall i, let b = nth witness BP.bb0{1} i in 
                         let b'= nth witness BPRIV_SB.bb{2} i in
                0 <= i < size BP.bb0{1} /\ 
                BPRIV_SB.hvo{2}.[(b'.`3, b'.`2)] = None =>
                   b = b')/\
              (forall (c,l), mem BPRIV_SB.encL{2} (c,l) =>
                 exists id, mem BPRIV_SB.bb{2} (id,l,c))/\
              (forall (l,c), ! mem BPRIV_SB.encL{2} (c,l) =>
                 BPRIV_SB.hvo{2}.[(c,l)]  = None)/\
              (forall (id, id',c,l), mem BPRIV_SB.bb{2} (id,l,c)=>
                 mem BPRIV_SB.bb{2} (id',l,c) => id = id')/\     
              Some v0{1} = dec_cipher BP.sk{1} b0{1}.`2 b0{1}.`3 
                                      HRO.RO.m{1}).
      + inline *; wp; sp.
        call(_: ={glob HRO.RO, BP.pk}); first by sim. 
        wp.   
        exists* (glob E){1}, BP.pk{1}, BP.sk{1}, l{1}, v{1}; 
          elim * => ge pk1 sk1 l1 v1. 
        pose kp:=  (pk1= extractPk sk1).
        cut em_kp: kp \/ !kp by smt. 
        elim em_kp. 
        + move => h. 
          call{1} (Eenc_decL ge sk1 pk1 l1 v1 h).  
          by auto; progress; smt.
        - move => h.    
          conseq(_: _ ==> !(BP.pk{1} =extractPk BP.sk{1})); 
            progress.
          call{1} (Ee_ll HRO.RO HRO.RO_o_ll).
          by auto; progress; smt.

      (* Valid is true for (b{2}.`2,b{2}.`3), if there exists no id, such that 
               (id, b{2}.`2, b{2}.`3) is in bb{2} *)
      exists* b{2}; elim* =>b2.
      call (_: ={glob HRO.RO, glob C, BP.uL, BP.pk, arg} /\
             BP.bb1{1} = BPRIV_SB.bb{2} /\
             arg{2}.`1 = BPRIV_SB.bb{2} /\
             arg{2}.`3 = b2 ==>
             ={glob HRO.RO, glob C, BP.uL, BP.pk, res } /\
             BP.bb1{1} = BPRIV_SB.bb{2} /\
             (res{2} => forall id, ! mem BPRIV_SB.bb{2} (id,b2.`2,b2.`3))).
      + proc.
        call (_: ={glob HRO.RO}); first by sim.
        wp;while (={ i, bb, ev1, b} /\ 0<= i{2} /\
                  (!ev1{2} => forall id, 
                            !mem (take i{2} bb{2}) (id, b{2}.`2, b{2}.`3))). 
          auto; progress. 
          + by smt.
          + rewrite take_onth; first by done.
            rewrite mem_rcons in_cons -nor (H0 H3 id) //=.
            by smt.
          + by smt.
        by auto; progress; smt.
        (* end Valid *)

      auto;progress.  
      + by smt. + by smt. + by smt. 
      + case (0 <= i < size BPRIV_SB.bb{2}).
        + move => H18. 
          move: H13; rewrite nth_cat nth_cat. 
          have ->: (i < size BPRIV_SB.bb{2}) = true by smt.
          have ->: (i < size BP.bb0{1}) = true by smt.
          rewrite mem_cat //=. 
          progress.
          have Hd: (b{2}.`3, b{2}.`2) <> 
                   ((nth witness BPRIV_SB.bb{2} i).`3,
                    (nth witness BPRIV_SB.bb{2} i).`2). 
            cut t:= H9 H10 . 
            have Hx:= mem_nth witness BPRIV_SB.bb{2} i H18.
            have Hsx: !mem BPRIV_SB.bb{2} ((nth witness BPRIV_SB.bb{2} i).`1, 
                                            b{2}.`2, b{2}.`3) by smt.
            by smt. 
          by smt.
        - move => Hx. 
          have Hc: size BPRIV_SB.bb{2} <= i by smt.
          rewrite nth_cat nth_cat. 
          by smt.
      + case (0 <= i < size BP.bb0{1}). 
        + move => H18.
          move: H13; rewrite ?nth_cat.
          by smt.
        - move => Hx.
          have Hc: size BP.bb0{1} = i by smt.
          rewrite ?nth_cat //=.
          have ->: i < size BP.bb0{1} = false by smt.
          have ->: i < size BPRIV_SB.bb{2} = false by smt.
          by smt.
      + rewrite cats1 mem_rcons in_cons in H11. 
        case (mem BPRIV_SB.encL{2} (c, l0)). 
        + progress.  
          by smt.
        - move => Hx. 
          have Hc: (c, l0) = (b{2}.`3, b{2}.`2) by smt.
          exists b{2}.`1.
          rewrite cats1 mem_rcons in_cons. 
          by smt.
      + by smt.
      + case (mem BPRIV_SB.bb{2} (id0, l0, c)).
        + case (mem BPRIV_SB.bb{2} (id', l0, c)). 
          + by smt.
          - move => H17 H18. 
            have H19: b{2} = (id', l0, c) by smt.
            by smt.
        - move => H17.
          have H18: b{2} = (id0, l0, c) by smt.
          move: H11 H12; rewrite cats1 mem_rcons;
          by smt.
      + by smt. 

    (*  A.a1: cast oracle *)
    + proc.   
      if; auto.
      inline Right.l_or_r; sp.

      (* Valid gives true if, for any id we have (id,b{2}.`2,b{2}.`3) not in bb{2} *)
      exists* b{2}; elim* =>b2;
      call (_: ={glob HRO.RO, glob C, BP.uL, BP.pk, arg} /\
             BP.bb1{1} = BPRIV_SB.bb{2} /\
             arg{2}.`1 = BPRIV_SB.bb{2} /\
             arg{2}.`3 = b2 ==>
             ={glob HRO.RO, glob C, BP.uL, BP.pk, res } /\
             BP.bb1{1} = BPRIV_SB.bb{2} /\
             (res{2} => forall id, ! mem BPRIV_SB.bb{2} (id,b2.`2,b2.`3))).
      + proc.
        call (_: ={ glob HRO.RO}); first by sim.
        wp;while (={ i, bb, ev1, b} /\ 0<= i{2} /\
                  (!ev1{2} => forall id, 
                              !mem (take i{2} bb{2}) (id, b{2}.`2, b{2}.`3))). 
          auto; progress. 
          + by smt.
          + rewrite take_onth; first by done.
            rewrite mem_rcons in_cons -nor (H0 H3 id) //=. 
            by smt.
          + by smt.
        by auto; progress; smt.
        (* end Valid *)
     
      auto; progress.   
      + by smt.  + by smt. 
      + case (0 <= i < size BPRIV_SB.bb{2}).
        + move => H18. 
          move : H12; rewrite ?nth_cat. 
          by smt.
        - move => H18.
          move: H12.
          rewrite ?nth_cat.
          by smt.
      + case (0 <= i < size BP.bb0{1}). 
        + move => H18.
          move: H12.
          rewrite ?nth_cat.
          by smt.
        - by smt.
      + by smt.
      + case (mem BPRIV_SB.bb{2} (id, l, c)).
        + case (mem BPRIV_SB.bb{2} (id', l, c)).
          + by smt.
          - move => H16 H17. 
            have H18: b{2} = (id', l, c) by smt.
            by smt.
        - move => H16.
          have H17: b{2} = (id, l, c) by smt.
          move: H10 H11; rewrite cats1 mem_rcons.
          by smt.

    (* A.a1: board, H, S oracle *)
    + by proc; inline *; auto.
    + by proc; auto; progress; smt.    
    + by conseq So_ll2; progress.

  (* before  A.a1 *)
  inline BPRIV_R(MV(E, P, Ve, C), A, HRO.RO, G, S).V.setup
    BPRIV_SB(E, C, A, HRO.RO, Right, S).MV.setup.
  wp; while (={ i0, uL}/\ nr{1} =n{2}).
    by auto.
  call{1} (Ekgen_extractPk HRO.RO).
  wp; call(_: true).
  call{1} Gi_ll.
  call (_: true ==> ={glob HRO.RO}).
    by sim. 
  by auto; progress; smt.
qed.

(* lemma bounding reduction from BPRIV single board to IND1CCA multi-challenge *)
local lemma sgBoard_ind1CCA (LR<: LorR {BS, BP, BPRIV_SB, BIND, HRO.RO, G, 
                                    E, S, C, A}) &m:
  `|Pr[BPRIV_SB(E, C, A, HRO.RO, LR, S).main() 
         @ &m: res ] -
    Pr[Ind1CCA(E,BIND(MV(E,P,Ve,C), A, S),HRO.RO,LR).main() 
         @ &m: res /\ size BS.encL <= n ]|
  <=Pr[Ind1CCA(E,BIND(MV(E,P,Ve,C), A, S),HRO.RO,LR).main() 
         @ &m: BIND.badQ <> None /\ 0<= oget BIND.badQ < n] .
proof.
  byequiv (_: = {glob A, glob C, glob S, glob E} ==>
                (BPRIV_SB.badQ{1} = BIND.badQ{2}) /\
                (!(BIND.badQ{2} <> None /\ 0<= oget BIND.badQ{2} < n) =>              
                   (res{1} <=> 
                    (res{2} /\ size BS.encL{2} <= n))))
          : (BPRIV_SB.badQ <> None /\ 0<= oget BPRIV_SB.badQ < n) =>//. 
  proc.
  inline Ind1CCA(E, BIND(MV(E, P, Ve, C), A, S), HRO.RO, LR).A.main.
  swap{1} 7 6.
  swap{1} 3 10.

  seq 11 18: (={glob A, glob C, glob E, glob S, 
                HRO.RO.m, BP.uL, BP.pk, BP.qVo, 
                BP.qCa} /\ 
             !BS.decQueried{2}            /\
             BPRIV_SB.bb{1}  = BIND.bb{2}/\
             BPRIV_SB.hvo{1} = BIND.hvo{2}/\
             BP.pk{1} = BS.pk{2} /\
             BP.sk{1} = BS.sk{2} /\
             size BS.encL{2} <= n /\
             BPRIV_SB.badQ{1} = BIND.badQ{2} /\ 
             (BIND.badQ{2} <> None =>
                0<= oget BIND.badQ{2} < n) /\
             (BIND.badQ{2} = None => 
                BPRIV_SB.encL{1} = BS.encL{2})/\
             BIND.encL{2}=BS.encL{2}).

    (* A.a1 call *)
    call (_: ={glob C, glob E, glob S, glob HRO.RO,
             BP.uL, BP.pk, BP.qVo, BP.qCa} /\ 
             !BS.decQueried{2}            /\
             BPRIV_SB.bb{1}  = BIND.bb{2}/\
             BPRIV_SB.hvo{1} = BIND.hvo{2}/\
             BP.pk{1} = BS.pk{2} /\
             BP.sk{1} = BS.sk{2} /\
             size BS.encL{2} <= BP.qVo{2} /\
             BP.qVo{2} <= n /\
             BPRIV_SB.badQ{1} = BIND.badQ{2} /\
             (BIND.badQ{2} <> None =>
                0<= oget BIND.badQ{2} < n) /\
             (BIND.badQ{2} = None => 
                BPRIV_SB.encL{1} = BS.encL{2})/\
             BIND.encL{2}=BS.encL{2}).               

    (* A.a1: vote oracle *)
    + proc.
      if =>//=; sp.
      if; auto; last by progress; smt.
      call(_: ={BP.pk, BP.uL, glob HRO.RO, glob C}).
      + call (_: ={glob HRO.RO}); first by sim.
          wp; while (={i,bb,b, ev1}).
          + by auto; progress; smt.
        by auto; progress; smt.
      inline Ind1CCA_Oracles(E, HRO.RO, LR).enc 
        BPRIV_SB(E, C, A, HRO.RO, LR, S).MV.vote.
      wp; call(_: ={glob HRO.RO}); first by sim. 
      wp; call(_: true).   
      by auto; progress; smt.

    (* A.a1: cast oracle *)
    + proc.
      if; auto.
      call(_: ={BP.pk, BP.uL, glob HRO.RO, glob C}).
      + call (_: ={glob HRO.RO}); first by sim.
        wp; while (={i,bb,b, ev1}).
        + by auto; progress; smt.
        by auto; progress; smt.
      by auto; progress; smt.

    (* A.a1: board, H, S oracles *)
    + by proc; auto.
    + by proc; auto; progress; smt.    
    + by conseq So_ll2; progress.

    (* before A.a1 call *)  
    inline BPRIV_SB(E, C, A, HRO.RO, LR, S).MV.setup.
    swap{1} 9 6.
    call(_: true); wp.
    while (uL{1} = BP.uL{2} /\ i0{1} = i{2} /\ n{1} = part).
      by auto. 
    swap{1} 12 -3.
    wp; call (_: ={glob HRO.RO}).
    wp; call(_: true ==> ={glob HRO.RO}).
      by sim.
    by auto; progress; smt.

  (* continue seq *)
  exists* BIND.badQ{2}; elim* => bad2.
  cut em_bad: (bad2= None) \/ (bad2 <> None) by smt. 
  elim em_bad. 
  (* good event *)
  + move => h. 
    wp; call(_: ={BP.r, glob S, glob HRO.RO} /\ 
                BPRIV_SB.bb{1}  = BIND.bb{2});
     [1..3: by sim].

    call (_: true). auto; progress.
    auto; while (={ glob HRO.RO, ubb, i} /\  0<= i{1} /\
               BP.sk{1} = BS.sk{2} /\ 
               bad2 = BIND.badQ{2} /\
               BP.pk{1} = BS.pk{2} /\
               BPRIV_SB.bb{1} = BIND.bb{2} /\
               BPRIV_SB.hvo{1} = BIND.hvo{2} /\
               BPRIV_SB.badQ{1} = BIND.badQ{2} /\
               (BIND.badQ{2} = None => 
                 BPRIV_SB.encL{1} = BS.encL{2}) /\
               BIND.encL{2}=BS.encL{2} /\
               mL{2} = map (fun (b0 : ident * label * cipher) =>
                     if ! mem BS.encL{2} (b0.`3, b0.`2) 
                     then dec_cipher BS.sk{2} b0.`2 b0.`3 
                                     HRO.RO.m{2}
                     else None) BIND.bb{2}).
      wp; sp.
      if{1}; auto; last by progress; smt. 
      exists* (glob E){1}, b{1}, BP.sk{1} ; elim* => ge1 b1 sk1.
      call{1} (Edec_Odec ge1 sk1 b1.`2 b1.`3). 
      auto; progress.
      + have Hm: 0 <= i{2}  < size BIND.bb{2} by done.
        rewrite (nth_map witness witness _ i{2} _ Hm) //=. 
        by smt.
      + by smt. + by smt. + by smt.

    inline Ind1CCA_Oracles(E, HRO.RO, LR).dec.
    wp; sp.
    exists* (glob E){2}, cL0{2}; elim* =>ge cLL.
    if{2}; auto.
    while{2} (0 <= i0{2} <= size cL0{2} /\ ge = (glob E){2} /\
              (mL0{2} = map (fun (cl: cipher* label) =>
                        if !mem BS.encL{2} cl
                        then dec_cipher BS.sk{2} cl.`2 cl.`1 HRO.RO.m{2}
                        else None) (take i0{2} cL0{2})))
             (size cL0{2} - i0{2}); progress. 
      wp; sp.
      exists * c, l, BS.sk{hr}; elim* => c2 l2 sk2.
      call{1} (Edec_Odec ge sk2 l2 c2).
      auto; progress. 
      + by smt. + by smt.  
      + have H5: 0 <= i0{hr}  < size cL0{hr} by smt.
        rewrite (take_nth witness) 1: H5 // -cats1.
        by smt.
      + by smt. + by smt. + by smt.
      + have Hx: 0 <= i0{hr}  <  size cL0{hr} by done.
        rewrite (take_nth witness) 1: Hx // -cats1.
        by smt.
      + by smt.

    auto; progress. 
    + by smt. by smt. by smt.
    + have ->>: i0_R = size (remID BIND.bb{2}) by smt. 
      rewrite !take_size(remid_map BIND.bb{2}) -map_comp. 
      by rewrite /ExtEq.(==) //.
    
  (* bad event *)
  move => h.     
  wp; conseq (_: _ ==> BIND.badQ{2} <> None).
    by progress; smt. 
  (* A.a2 calls *)
  call{1} (Aa2_ll (<:BPRIV_SB(E, C, A, HRO.RO, LR, S).O) _ _ _).
  + proc; auto.
  + proc; auto.
  + apply So_ll.  
  call{2} (Aa2_ll (<:BIND(MV(E, P, Ve, C), A, S, 
                     Ind1CCA_Oracles(E, HRO.RO, LR)).O) _ _ _).
  + proc; auto.
  + proc; auto.
  + apply So_ll. 
  
  call{1} Sp_ll.  
  call{2} Sp_ll.
  wp; rnd{1}; rnd{2}.
  conseq (_: _ ==> BIND.badQ{2} <> None).
    progress; smt.
    
  while{1} (true) (size BPRIV_SB.bb{1} -i{1}); progress.
    sp; if{1}; auto.
      call{1}( Ed_ll HRO.RO HRO.RO_o_ll).
      by auto; progress; smt.
    by progress; smt.
  while{2} (true) (size  BIND.bb{2} - i{2}); progress.          
    by auto; progress; smt.
  inline Ind1CCA_Oracles(E, HRO.RO, LR).dec.
  wp; sp.
  if{2}; auto.
  while{2} (true) (size cL0{2} - i0{2}); progress.
    wp; call{1} (Ed_ll HRO.RO HRO.RO_o_ll).    
    by auto; progress; smt.
  by auto; progress; smt. 
qed. 

(* guess bad oracle *)
clone  Ex_Plug_and_Pray as EPP with
  type tin  <- unit,
  type tres <- bool,
  op bound  <- n
proof bound_pos. 
realize bound_pos. by apply n_pos.  qed. 

(* Lemma that replaces an adversary that changes badQ to true when 
         a honest ballot fails the valid algorithm with and adversary 
         that guesses when badQ will fail *)
local lemma guessBadQ (LR<: LorR {BP, BS, HRO.RO, BIND, A, C, E, S}) &m:
  1%r/ n %r * 
  Pr[Ind1CCA(E,BIND(MV(E,P,Ve,C), A, S),HRO.RO,LR).main() 
         @ &m: BIND.badQ <> None /\ 0<= oget BIND.badQ < n] 
  = 
  Pr[EPP.Guess(Ind1CCA(E,BIND(MV(E,P,Ve,C), A, S),HRO.RO,LR)).main() 
         @ &m: BIND.badQ <> None /\ 0<= oget BIND.badQ < n /\ fst res = oget BIND.badQ ].
proof.
  cut := EPP.PBound (Ind1CCA(E,BIND(MV(E,P,Ve,C), A, S), HRO.RO, LR))
          (fun g b => let (gv1, gv2, bad, gv3, gv4, gv5, gv6, gv7, 
                           gv8, gv9, gv10, gv12, gv13, gv14, 
                           gv15, gv16, gl1, gl2, gl3, gl4)= g in
             (bad <> None /\ 0<= oget bad < n))
          (fun g b => let (gv1, gv2, bad, gv3, gv4, gv5, gv6, gv7,
                           gv8, gv9, gv10, gv12, gv13, gv14,
                           gv15, gv16, gl1, gl2, gl3, gl4)= g in
           oget bad) () &m. 
  simplify.
  move => ->. 
  by rewrite Pr[mu_eq]; progress; smt. 
qed.

(* lemma bounding the change from Ind1CCA.badQ = Guess.i: int option to 
         Ind1CCA.bad: bool if Ind1CCA.ibad = Guess.i *)
lemma guess_to_bad (LR<: LorR {BS, BP, BIND, BIND2, HRO.RO, E, S, C, A}) &m:
  Pr[EPP.Guess(Ind1CCA(E, BIND(MV(E,P,Ve,C), A, S),HRO.RO, LR)).main() 
         @ &m: BIND.badQ <> None /\ 0<= oget BIND.badQ < n /\ 
               fst res = oget BIND.badQ ]
  <=
  Pr[Ind1CCA(E,BIND2(MV(E,P,Ve,C), A, S), HRO.RO, LR).main() @ &m: BIND2.bad].
proof.
  byequiv=>//=.
  proc.
  inline Ind1CCA(E, BIND (MV(E, P, Ve, C), A, S), HRO.RO, LR).main
         Ind1CCA(E, BIND2(MV(E, P, Ve, C), A, S), HRO.RO, LR).A.main
         Ind1CCA(E, BIND (MV(E, P, Ve, C), A, S), HRO.RO, LR).A.main.
  
  seq 20 17: (={glob A, glob C, glob E, glob S, glob HRO.RO, BP.uL, 
                BP.pk, BP.qVo, BP.qCa} /\ 
              (BIND.badQ{1} <> None /\ 
              fst (i{1}, b'{1}) = oget BIND.badQ{1}
              => BIND2.bad{2})).
    (* A.a1 call *)  
    call(_: ={glob C, glob E, glob S, glob HRO.RO, BP.uL, 
               BP.pk, BP.qVo, BP.qCa, BS.pk} /\ 
          BIND.bb{1} = BIND2.bb{2}/\
          (BIND.badQ{1} <> None /\ 
           BIND2.ibad{2} = oget BIND.badQ{1}=>
             BIND2.bad{2})). 
    
    (* A.a1: vote call *)
    + proc.
      if =>//=; sp.
      if; auto.
      call(_: ={glob HRO.RO, glob C, BP.uL, BP.pk});
        first by sim.
      inline *; wp.
      call (_: ={ glob HRO.RO});
        first by sim.    
      wp; call (_: true).
      by auto; progress; smt.

    (* A.a1: cast call *)
    + proc. 
      if; auto.
      call(_: ={glob HRO.RO, glob C, BP.uL, BP.pk});
        first by sim.
      by auto.

    (* A.a1: board, H, S calls *)
    + by proc; auto.
    + by proc; auto.
    + by conseq So_ll2.


    (* before A.a1 *)
    call(_: true).
    while (={BP.uL} /\i0{1} = i{2}). 
      by auto.
    swap{2} 6 -5.
    wp; call(_: ={glob HRO.RO}).
    call(_: true ==> ={glob HRO.RO}).
      by sim.
    by auto; progress; smt.
 
  (* after A.a1 call *)
  wp; call{1} (Aa2_ll (<: BIND(MV(E, P, Ve, C), A, S, 
                      Ind1CCA_Oracles(E, HRO.RO, LR)).O) _ _ _).
  + by proc; auto.
  + by proc; auto.
  + by conseq So_ll.
  call{1} Sp_ll.
  auto; while{1} (true) (size BIND.bb{1} - i0{1}); progress.
    by auto; progress; smt.
  inline Ind1CCA_Oracles(E, HRO.RO, LR).dec.
  sp; wp.
  if{1}; auto.
    while{1} (true) (size cL0{1} - i1{1}); progress.
      wp; call{1} (Ed_ll HRO.RO HRO.RO_o_ll).   
      by auto; progress; smt.
    by auto; progress; smt.
  by progress; smt.
qed.

(* Lemma that reduces Ind1CCA.bad to strong correctness' *)
local lemma bound_Scorr (LR <: LorR {BS, BP, BSC, BIND2, BSCorr, 
                               HRO.RO, A, E, C, S}) &m: 
islossless LR.l_or_r => 
  Pr[Ind1CCA(E,BIND2(MV(E,P,Ve,C), A, S), HRO.RO,LR).main() 
         @ &m: BIND2.bad]
  <=
  Pr[SCorr' (MV(E,P,Ve,C), BSCorr(MV(E,P,Ve,C),A, LR), HRO.RO, S).main() 
         @ &m: BSC.valid].
proof.
  move=> LR_ll.
  byequiv(_: ={glob A, glob C, glob E, glob S, glob HRO.RO}==>_)  =>//.
  proc. 
  inline Ind1CCA(E, BIND2(MV(E, P, Ve, C), A, S), HRO.RO, LR).A.main
    SCorr'(MV(E, P, Ve, C), BSCorr(MV(E, P, Ve, C), A, LR), HRO.RO, S).V.setup
    SCorr'(MV(E, P, Ve, C), BSCorr(MV(E, P, Ve, C), A, LR), HRO.RO, S).A.main.
  wp.  
  call(_: BSCorr.ibad < BP.qVo
         ,={glob C, glob E, glob S, glob HRO.RO, 
            BP.uL, BP.qVo, BP.qCa, BP.pk}/\
          BS.pk{1} = BP.pk{2}/\
          BP.pk{2} = BSC.pk{2}/\
          BP.uL{2} = BSC.uL{2}/\
          BIND2.bb{1}  = BSCorr.bb{2}/\
          BIND2.ibad{1}= BSCorr.ibad{2}/\
          BIND2.bad{1} = BSC.valid{2} /\
          size BSCorr.bb{2} <= BP.qVo{2}+BP.qCa{2}/\
          BSCorr.ibad{2} < n /\
          BP.qVo{2} <= n /\
          BP.qCa{2} <= k
         ,BIND2.bad{1} = BSC.valid{2} /\
          BIND2.ibad{1} < BP.qVo{1}).

    (* A.a1 lossless *)
    + by apply Aa1_ll.

    (* A.a1: vote oracle *)    
    + proc. 
      if{1}=>//=; sp. 
      + if{2}. 
        + sp.
          if; auto; last by auto; progress; smt.
          call(_: ={ glob HRO.RO, glob C, BP.pk, BP.uL}); 
            first by sim.
          inline Ind1CCA_Oracles(E, HRO.RO, LR).enc
            BSCorr(MV(E, P, Ve, C), A, LR, 
                   SCorr_Oracle'(MV(E, P, Ve, C), HRO.RO, S)).V.vote.
          wp; call (_: ={glob HRO.RO});
            first by sim.
          wp; call (_: true). 
          by auto; progress; smt. 
       - rcondt{2} 1; first by auto; progress; smt.
         inline SCorr_Oracle'(MV(E, P, Ve, C), HRO.RO, S).test.
         if{1}; progress. 
         + (* good side: l{1} = l0{2} and <> None *)
           inline Ind1CCA_Oracles(E, HRO.RO, LR).enc.
           swap{1} 5 -4.
           seq 1 1: (BP.uL{1}.[id{1}] <> None /\
                BP.qVo{2} = BSCorr.ibad{2} /\
                ={id, v0, v1} /\
                ={glob C, glob E, glob S, HRO.RO.m, 
                  BP.qVo, BP.qCa, BP.uL, BP.pk} /\
                BS.pk{1} = BP.pk{2} /\
                BP.pk{2} = BSC.pk{2}/\
                BP.uL{2} = BSC.uL{2}/\
                BIND2.bb{1} = BSCorr.bb{2} /\
                BIND2.ibad{1} = BSCorr.ibad{2} /\ 
                BIND2.bad{1} = BSC.valid{2}/\
                BP.qVo{1} < n /\
                BP.qCa{2} <= k /\
                BSCorr.ibad{2} < n /\
                size BSCorr.bb{2} <= BP.qVo{2} + BP.qCa{2}/\
                ={l_or_r}). 
             by call(_: true); auto; smt.      

           sp; rcondt{2} 1; first
             by progress; auto; progress; smt.
           sp; rcondt{2} 1; first    
             by progress; auto.
           seq 5 3: ( l0{2} = BP.uL{2}.[id0{2}] /\
                 l{1} = oget BP.uL{1}.[id{1}] /\
                 l{1} = l0{1} /\

                 ={id, v0, v1} /\
                 id0{2} = id{2} /\

                 BS.pk{1} = BP.pk{2} /\
                 BP.pk{2} = BSC.pk{2}/\
                 BP.uL{2} = BSC.uL{2}/\
                 bb{2} = BSCorr.bb{2} /\
                 BIND2.bb{1} = BSCorr.bb{2} /\
                 BIND2.ibad{1} = BSCorr.ibad{2} /\ 
                 BIND2.bad{1} = BSC.valid{2}/\
                 BP.qVo{2} = BSCorr.ibad{2} /\
                 ={glob C, glob E, glob S, HRO.RO.m, 
                   BP.qVo, BP.uL, BP.qCa, BP.pk} /\
                 BP.qVo{1} < n /\
                 BP.qCa{2} <= k /\ 
                 size BSCorr.bb{2} <= BP.qVo{2} + BP.qCa{2} /\
                 ev{1} = ev0{2}).

             call(_: ={ glob HRO.RO, glob C, BP.uL, BP.pk}); 
               first by sim.
             inline* ; wp.
             call(_: ={glob HRO.RO});
               first by sim.
             by auto; progress.
           by auto; progress; smt.
         - seq 0 6: ( BP.uL{1}.[id{1}] = None /\
                 BP.qVo{2} = BSCorr.ibad{2} /\
                 BS.pk{1} = BP.pk{2} /\
                 BP.pk{2} = BSC.pk{2}/\
                 BP.uL{2} = BSC.uL{2}/\
                 BIND2.bb{1} = BSCorr.bb{2} /\
                 BIND2.ibad{1} = BSCorr.ibad{2} /\ 
                 BIND2.bad{1} = BSC.valid{2}/\
                 ={id, v0, v1} /\
                 ={glob C, glob E, glob S, HRO.RO.m, 
                   BP.qVo, BP.qCa, BP.uL, BP.pk}/\
                 id0{2}= id{2} /\
                 v2{2} = v{2} /\ 
                 bb{2} =  BSCorr.bb{2}/\
                 ev0{2}/\
                 size BSCorr.bb{2} <= BP.qVo{2}+ BP.qCa{2} /\
                 BP.qVo{1} < n /\
                 BP.qCa{2} <= k). 
             by wp; call{2} LR_ll; auto; smt.
           rcondt{2} 1; first
             by progress; auto; progress; smt.
           sp; if{2} => //=; last by auto; progress; smt.
           inline *; wp. 
           call{2} (Co_ll HRO.RO HRO.RO_o_ll).
           wp; while{2} (0 <= i{2} <= size bb0{2})
                      (size bb0{2} - i{2}); progress.  
             by auto; progress; smt.
           wp; call{2} (Ee_ll HRO.RO HRO.RO_o_ll).
           by auto; progress; smt.
 
    (* closing the first if{1} *)
     -  sp; rcondf{2} 1=>//=; first by auto; smt.
     rcondf{2} 1=>//=; first by auto; smt.

    (* A.a1: vote lossless *)    
    + progress; proc. 
      if =>//=.
      if=>//=; last by auto; smt.   
      inline *; wp. 
      call{1} (Co_ll (Ind1CCA_Oracles(E, HRO.RO, LR)) 
                   HRO.RO_o_ll).
      wp; while (0 <= i <= size bb)
              (size bb - i); progress.  
        by auto; progress; smt.
      wp; call (Ee_ll HRO.RO HRO.RO_o_ll).
      wp; call LR_ll.  
      by auto; progress; smt.   

    (* A.a1: vote preserves bad *)
    + progress; proc.
      if; auto. 
      + if=>//=; last by auto; progress; smt.
        inline*; wp.
        call (Co_ll (Hwrap(SCorr_Oracle'(MV(E, P, Ve, C), HRO.RO, S))) 
                  HRO.RO_o_ll).
        wp; while{1} (0 <= i <= size bb)
                 (size bb - i); progress.  
          by auto; progress; smt.
        wp; call (Ee_ll (Hwrap(SCorr_Oracle'(MV(E, P, Ve, C), HRO.RO, S))) 
                      HRO.RO_o_ll).
        wp; call LR_ll.
        by auto; progress; smt.
      - if; auto.
        inline*.
        seq 6: (ev0 /\ id0 = id /\ v2 = v /\
            BSCorr.ibad < BP.qVo/\
            (BSC.qt < 1 => BIND2.bad{1} = BSC.valid)/\ 
            BIND2.ibad{1} < BP.qVo{1}/\
            ! BP.qVo < BSCorr.ibad /\
              BP.qVo = BSCorr.ibad)=>//. 
        + by wp; call LR_ll. 
        + if; auto.
          sp; if =>//=.
          wp; call (Co_ll HRO.RO HRO.RO_o_ll).
          wp; while{1} (0 <= i <= size bb0)
                   (size bb0 - i); progress.  
           by auto; progress; smt.
         wp; call (Ee_ll HRO.RO HRO.RO_o_ll). 
         by auto; progress; smt.
      by wp; hoare; call(_: true). 

    (* A.a1: cast call *)
    + proc.
      if =>//=.
      wp; call(_: ={ glob HRO.RO, glob C, BP.uL, BP.pk}). 
        by sim. 
      by auto; progress; smt. 

    (* A.a1: cast lossless *)
    + progress; proc.
      if=>//=. 
      inline *; wp.
      call (Co_ll (Ind1CCA_Oracles(E, HRO.RO, LR)) HRO.RO_o_ll).
      wp; while{1} (0 <= i <= size bb)
                 (size bb - i); progress. 
        by auto; progress; smt.
      by auto; progress; smt.

    (* A.a1: cast preserves bad *)
    + progress; proc.
      if=>//=.
      inline *; wp.
      call (Co_ll (Hwrap(SCorr_Oracle'(MV(E, P, Ve, C), HRO.RO, S))) 
                HRO.RO_o_ll).
      wp; while{1} (0 <= i <= size bb)
                 (size bb - i); progress.  
        by auto; progress; smt.
      by auto; progress; smt.

   (* A.a1 board *)
   + by proc; auto.
   + by progress; proc; auto.
   + by progress; proc; auto.

   (* A.a1 H *)
   + by proc; auto.
   + by progress; proc; auto.
   + by progress; proc; auto.

   (* A.a1 S *)
   + by conseq So_ll2.
   + by progress; conseq So_ll.
   + by progress; conseq So_ll. 
  
   (* before A.a1 *)
   swap{1} 16 -12.
   swap{2} 14 -4.
   wp; while (={i}/\ part = nr{2}/\ BP.uL{1} = uL{2}).
     by auto.
   auto. 
   call (_: true).
   wp; call (_: ={glob HRO.RO}).
   call (_: true ==> ={glob HRO.RO}). 
     by sim. 
   by auto; progress; smt.
qed.


(* strong correctness' adversary using strong correctness adversary *)
local module BSCorr'(LR : LorR, V : VotingScheme, SO : SCorr_Oracle) 
           = BSCorr(V,A,LR,SO).

(* Lemma equivalence strong correctness' to strong correctness *)
local lemma scorrRed (LR<: LorR { BS, BP, BIND, BIND2, BSCorr, BSC, HRO.RO, A, C, E, P, Ve, S}) &m:
  islossless LR.l_or_r =>
   Pr[SCorr' (MV(E,P,Ve,C), BSCorr(MV(E,P,Ve,C),A, LR), HRO.RO, S).main() 
         @ &m: BSC.valid] =
   Pr[SCorr (MV(E,P,Ve,C), BSCorr(MV(E,P,Ve,C),A, LR), HRO.RO, S).main() 
         @ &m: BSC.valid].
proof.
  move => LR_ll.
  have ->: Pr[SCorr'(MV(E,P,Ve,C), BSCorr(MV(E,P,Ve,C),A,LR),HRO.RO,S).main() @ &m: BSC.valid]
         = Pr[SCorr'(MV(E,P,Ve,C), BSCorr'(LR,MV(E,P,Ve,C)),HRO.RO,S).main() @ &m: BSC.valid].
    by byequiv=> //=; sim.
  have ->: Pr[SCorr(MV(E,P,Ve,C), BSCorr(MV(E,P,Ve,C),A,LR),HRO.RO,S).main() @ &m: BSC.valid]
         = Pr[SCorr(MV(E,P,Ve,C), BSCorr'(LR,MV(E,P,Ve,C)),HRO.RO,S).main() @ &m: BSC.valid].
    by byequiv=> //=; sim. 
  rewrite (VSmv.SCorr_vers HRO.RO S (MV(E,P,Ve,C)) (<: BSCorr'(LR)) _ _ _ _ _ _ &m).
  
  + move => uL pk &m0 Hm.
    byphoare (_: BSC.uL = arg.`2 /\ BSC.qt = 0 ==> _)=>//=.
    proc. 

    (* A.a1 call *)
    call (_: BP.uL = BSC.uL/\
             (BP.qVo <=  BSCorr.ibad => BSC.qt = 0 )/\
             (BSCorr.ibad < BP.qVo => BSC.qt <= 1)).
     + exact Aa1_ll. 
     + proc.
       if =>//=.
       + if =>//=; last by auto; progress; smt.
         inline *.
         wp; call (Co_ll (Hwrap(SCorr_Oracle'(MV(E, P, Ve, C), HRO.RO, S))) HRO.RO_o_ll).
         wp; while (true) (size bb -i); progress.
           by auto; progress; smt.
         wp; call (Ee_ll (Hwrap(SCorr_Oracle'(MV(E, P, Ve, C), HRO.RO, S))) HRO.RO_o_ll).
         wp; call LR_ll. 
         by auto; progress; smt.
 
       - if=>//=.
         seq 1 : (BP.uL = BSC.uL /\
                (BP.qVo <=  BSCorr.ibad => BSC.qt = 0 )/\
                (BSCorr.ibad < BP.qVo => BSC.qt <= 1)/\
                BP.qVo = BSCorr.ibad)=>//=. 
          + by call LR_ll; auto; smt.
          + inline *.
            sp; if =>//=; last by auto; progress; smt. 
            sp; if =>//=; last by auto; progress; smt.
            wp; call (Co_ll HRO.RO HRO.RO_o_ll).
            wp; while (true) (size bb -i); progress.
              by auto; progress; smt.
            wp; call (Ee_ll HRO.RO HRO.RO_o_ll). 
            by auto; progress; smt.  
         by hoare; call (_: true); auto; smt.   

     + proc.
       if=>//=.
       inline *. 
       wp; call (Co_ll (Hwrap(SCorr_Oracle'(MV(E, P, Ve, C), HRO.RO, S))) HRO.RO_o_ll).
       wp; while (true) (size bb -i); progress.
         by auto; progress; smt.
       by auto; progress; smt.

     + proc; auto.
  
     + conseq HRO.RO_o_ll.
     + conseq So_ll.

    by auto; progress; smt. 
 
    (* BSCorr' lossless *)
    + move => V O Oh_ll Og_ll Ot_ll //=.  
      proc.
      call (_: true).
      + exact Aa1_ll.
      + proc.
        if=>//=. 
        + if=>//=; last by wp.   
          wp; call (Vval_ll V (Hwrap(O)) (Gwrap(O)) Oh_ll Og_ll). 
          call (Vvot_ll V (Hwrap(O)) (Gwrap(O)) Oh_ll Og_ll).   
          by wp; call LR_ll; wp.
        - if =>//=. 
          by wp; call Ot_ll; wp; call LR_ll.        
      + proc. 
        if=>//=. 
        by wp; call (Vval_ll V (Hwrap(O)) (Gwrap(O)) Oh_ll Og_ll).
      + proc; auto.
      + exact Oh_ll.  
      + exact Og_ll.    
    by auto; smt.
          
    (* HRO.RO.o, S.o, MV.vote, lossless*)
    + by exact HRO.RO_o_ll. 
    + by exact So_ll. 
    + by progress; proc; call (Ee_ll H H0).

    (* MV.valid lossless *)
    + progress; proc.       
      call (Co_ll H H0). 
      wp; while (true) (size bb -i); progress.
        by auto; progress; smt.
      by auto; progress; smt.
  by done.
qed.

(* Lemma bound Ind1CCA.bad by strong correctness *)
local lemma bound_Ind1CCAbad 
  (LR<: LorR { BS, BP, BSC, BIND, BIND2, BSCorr, HRO.RO, A, C, Ve, P, E, S}) &m:
  islossless LR.l_or_r =>
  Pr[Ind1CCA(E,BIND(MV(E,P,Ve,C), A, S),HRO.RO,LR).main() 
         @ &m: BIND.badQ <> None /\ 0<= oget BIND.badQ < n]
  <= n%r *
  Pr[SCorr (MV(E,P,Ve,C), BSCorr(MV(E,P,Ve,C),A, LR), HRO.RO, S).main() 
         @ &m: BSC.valid].
proof.
  move=> LR_ll.
  pose a:= Pr[Ind1CCA(E, BIND(MV(E, P, Ve, C), A, S), HRO.RO, LR).main
              () @ &m : BIND.badQ <> None /\ 0 <= oget BIND.badQ < n].
  pose b:= Pr[SCorr(MV(E, P, Ve, C), BSCorr(MV(E, P, Ve, C), 
             A, LR), HRO.RO, S).main() @ &m : BSC.valid].
  have ->: (a <= n%r * b) <=> 1%r/ n %r * a <= b.
    progress; smt. 
  rewrite /a /b.
  rewrite (guessBadQ LR &m).        
  rewrite -(scorrRed LR &m LR_ll).
  cut t2:= guess_to_bad LR &m. 
  cut t3:= bound_Scorr LR &m LR_ll.
  by smt.
qed.

(* Lemma bounding diff of BPRIV single board and IND1CCA, with strong correctness *)
local lemma sgBoard_scorr 
  (LR <:LorR {BS, BP, BSC, BPRIV_SB, BIND, BIND2, BSCorr, HRO.RO, A, C, E, G, Ve, P, S}) &m:
  islossless LR.l_or_r =>
 `|Pr[BPRIV_SB(E, C, A, HRO.RO, LR, S).main() @ &m :res] -
   Pr[Ind1CCA(E, BIND(MV(E, P, Ve, C), A, S), HRO.RO, LR).main () @ &m : 
        res /\ size BS.encL <= n]| 
 <= n%r *
   Pr[SCorr(MV(E,P,Ve,C), BSCorr(MV(E,P,Ve,C),A, LR), HRO.RO, S).main() @ &m: BSC.valid].
proof.
  move=> LR_ll.
  cut HLR:= (sgBoard_ind1CCA LR &m). 
  cut HB:= (bound_Ind1CCAbad LR &m LR_ll). 
  by smt.
qed.
 
(* Lemma lossless constructed IND1CCA adversary *)
local lemma BINDmain_ll (IO <: Ind1CCA_Oracles{BIND(MV(E, P, Ve, C), A, S)}):
  islossless IO.enc =>
  islossless IO.dec =>
  islossless IO.o =>
  islossless BIND(MV(E, P, Ve, C), A, S, IO).main.
proof.
  move => IOe_ll IOd_ll IOo_ll.
  proc.
  call (Aa2_ll (<: BIND(MV(E, P, Ve, C), A, S, IO).O) _ _ _) =>//.
  + by proc; auto.
  + by apply So_ll.
  wp; call{1} Sp_ll.
  wp; rnd; while{1} (true) (size BIND.bb - i); progress.
    by auto; progress; smt.
  call{1} IOd_ll.
  wp.
  call (Aa1_ll (<: BIND(MV(E, P, Ve, C), A, S, IO).O) _ _ _ _ _) =>//.
  + proc. 
    if =>//=.
    sp;if{1}; auto.
    inline *; wp; call{1} (Co_ll IO IOo_ll).
    wp; while{1} (0 <= i <= size bb)
                 (size bb - i); progress.
      by auto; progress; smt.
    wp; call{1} IOe_ll.
    by auto; progress; smt.
  + proc. 
    if; auto. 
    inline *; wp; call{1} (Co_ll IO IOo_ll).
    wp; while{1} (0 <= i <= size bb)
                 (size bb - i); progress.
      by auto; progress; smt.      
    by auto; progress; smt.   
  + by proc; auto.
  + by apply So_ll.
  call{1} Si_ll.
  wp; while{1} (0 <= i <= part)
               (part - i); progress.
    by auto; progress; smt.
  by auto; progress; smt.
qed.

(* Lemma apply the hybrid argument *)
local lemma hybrid &m  (H <: HOracle.Oracle { BP, BS, BPS, BIND, PKEvf.H.Count, 
                                PKEvf.H.HybOrcl, WrapAdv, G, E, S, Ve, P, C, A}):
  islossless H.init =>
  islossless H.o    =>
  `|Pr[Ind1CCA(E,BIND(MV(E,P,Ve,C), A, S),H,Left).main() 
            @ &m: res /\ size BS.encL <= n ] -
    Pr[Ind1CCA(E,BIND(MV(E,P,Ve,C), A, S),H,Right).main() 
            @ &m: res /\ size BS.encL <= n ]|
 = n%r *
  `|Pr[Ind1CCA(E,WrapAdv(BIND(MV(E,P,Ve,C), A, S),E,H),H,Left).main() 
            @ &m: res /\ WrapAdv.l <= n /\ size BS.encL <= 1 ] -
   Pr[Ind1CCA(E,WrapAdv(BIND(MV(E,P,Ve,C), A, S),E,H),H,Right).main() 
            @ &m: res /\ WrapAdv.l <= n /\ size BS.encL <= 1 ]|.
proof.
  move=> Hi_ll Ho_ll; rewrite eq_sym.
  cut Ht: forall (n a b : real), n >0%r => n * a = b <=> a = 1%r/n * b by progress; smt.  
  pose a:= `|Pr[Ind1CCA(E, WrapAdv(BIND(MV(E, P, Ve, C), A, S), E, H), H, Left).main
     () @ &m : res /\ WrapAdv.l <= n /\ size BS.encL <= 1] -
  Pr[Ind1CCA(E, WrapAdv(BIND(MV(E, P, Ve, C), A, S), E, H), H, Right).main
     () @ &m : res /\ WrapAdv.l <= n /\ size BS.encL <= 1]|.
  pose b:= `|Pr[Ind1CCA(E, BIND(MV(E, P, Ve, C), A, S), H, Left).main() @ &m :
     res /\ size BS.encL <= n] -
  Pr[Ind1CCA(E, BIND(MV(E, P, Ve, C), A, S), H, Right).main
     () @ &m : res /\ size BS.encL <= n]|.
  rewrite -/a -/b.
  rewrite (Ht n%r a b). 
    cut t:= n_pos.
    by smt.
  rewrite /a /b. 

  by apply (Ind1CCA_multi_enc H E  (BIND(MV(E, P, Ve, C), A, S)) Hi_ll Ho_ll
           (Ek_ll H) (Ee_ll H) (Ed_ll H) BINDmain_ll &m).
qed.

(* Lemma bounding |IBPRIV - BPRIV-R| by n* strong correctness and n* |IND1CCAL-IND1CCAR| *)
local lemma bound_MV_Ind1CCA &m:
  `|Pr[IBPRIV (MV(E,P,Ve,C), A, HRO.RO, G, S).main() @ &m : res ] -
    Pr[BPRIV_R(MV(E,P,Ve,C), A, HRO.RO, G, S).main() @ &m : res]|
  <= 
  n%r *
     Pr[SCorr(MV(E,P,Ve,C), BSCorr(MV(E,P,Ve,C),A, Left), HRO.RO, S).main() @ &m: BSC.valid] +
  n%r *
     Pr[SCorr(MV(E,P,Ve,C), BSCorr(MV(E,P,Ve,C),A, Right), HRO.RO, S).main() @ &m: BSC.valid]+
  n%r *
   `|Pr[Ind1CCA(E,WrapAdv(BIND(MV(E,P,Ve,C), A, S),E,HRO.RO),HRO.RO,Left).main() 
            @ &m: res /\ WrapAdv.l <= n /\ size BS.encL <= 1 ] -
     Pr[Ind1CCA(E,WrapAdv(BIND(MV(E,P,Ve,C), A, S),E,HRO.RO),HRO.RO,Right).main() 
            @ &m: res /\ WrapAdv.l <= n /\ size BS.encL <= 1 ]|.
proof.
  cut trig: forall (x y z w: real), `|x - y| <= `|x - z| +`|z - w |+ `|y - w| by smt. 
  cut HL:= (sgBoard_scorr Left &m _ ).
    by proc; auto.
  cut HR:= (sgBoard_scorr Right &m _).
    by proc; auto.
  (* back to H *)
  rewrite -(hybrid &m HRO.RO _ _).
  + exact/HRO.RO_init_ll/distr_h_out/is_finite_h_in.
  + exact/HRO.RO_o_ll.
  cut H:= trig 
      (Pr[BPRIV_SB(E, C, A, HRO.RO, Left , S).main() @ &m  : res])
      (Pr[BPRIV_SB(E, C, A, HRO.RO, Right, S).main() @ &m : res])
      (Pr[Ind1CCA(E,BIND(MV(E,P,Ve,C), A, S),HRO.RO,Left).main() @ &m: 
          res /\ size BS.encL <= n]) 
      (Pr[Ind1CCA(E,BIND(MV(E,P,Ve,C), A, S),HRO.RO,Right).main() @ &m: 
          res /\ size BS.encL <= n ]).
  by smt.
qed.

(* Lemma bounding BPRIV  *) 
lemma bpriv &m:
    `|Pr[BPRIV_L(MV(E, P, Ve, C), A, HRO.RO, G).main() @ &m : res ]-
      Pr[BPRIV_R(MV(E, P, Ve, C), A, HRO.RO, G, S).main() @ &m : res ]| 
<=
      Pr[VFR(E, BVFR(MV(E, P, Ve, C), A), R(E), HRO.RO, G).main() @ &m : res] +
      Pr[VFR(E, BVFR(MV(E, P, Ve, C), A), R(E), HRO.RO, S).main() @ &m : res] +
    `|Pr[ZK_L(R(E,HRO.RO), P, BZK(E, P, C, Ve, A, HRO.RO), G).main() @ &m : res] -
      Pr[ZK_R(R(E,HRO.RO), S, BZK(E, P, C, Ve, A, HRO.RO)).main() @ &m : res]|         +
n%r *
      Pr[SCorr(MV(E, P, Ve, C), BSCorr(MV(E, P, Ve, C), A, Left), HRO.RO, S).main() @ &m : BSC.valid] +
n%r *
      Pr[SCorr(MV(E, P, Ve, C), BSCorr(MV(E, P, Ve, C), A, Right), HRO.RO, S).main() @ &m : BSC.valid] +
n%r *
    `|Pr[Ind1CCA(E, WrapAdv(BIND(MV(E, P, Ve, C), A, S), E, HRO.RO), HRO.RO, Left).main
            () @ &m : res /\ WrapAdv.l <= n /\ size BS.encL <= 1] -
      Pr[Ind1CCA(E, WrapAdv(BIND(MV(E, P, Ve, C), A, S), E, HRO.RO), HRO.RO, Right).main
            () @ &m : res /\ WrapAdv.l <= n /\ size BS.encL <= 1]|.
proof.
  (* lemma bound_MV_MV' for BPRIV_L to IBPRIV  *)
  cut L:= bound_MV_MV' &m HRO.RO HRO.RO_o_ll relConstraint. 
  (* lemma bound_MV_Ind1CCA for IBPRIV to BPRIV_R *)
  cut R:= bound_MV_Ind1CCA &m. 

  cut trig: forall (a b c: real), `|a - b| <= `|a-c| + `|c -b| by smt.
  cut M:= trig 
         (Pr[BPRIV_L(MV(E, P, Ve, C), A, HRO.RO, G).main() @ &m : res])
         (Pr[BPRIV_R(MV(E, P, Ve, C), A, HRO.RO, G, S).main() @ &m : res])
         (Pr[IBPRIV (MV(E, P, Ve, C), A, HRO.RO, G, S).main() @ &m : res]).
  by smt. 
qed.

end section BPRIV.

(* ---------------------------------------------------------------------- *)
(* Strong Consistency  *)
section StrongConsistency.

declare module H : HOracle.Oracle 
                   { BP}.
declare module G : GOracle.Oracle 
                   { BP, HRO.RO, H}.
declare module E : Scheme        
                   { BP, H, G}.
declare module S : Simulator 
                   { HRO.RO, H, G, E}.
declare module Ve: Verifier
                   { HRO.RO, H, G, E, S}.
declare module P : Prover
                   { HRO.RO, H, G, E, S, Ve}.
declare module C: ValidInd       
                   { BP, HRO.RO, H, G, E, S, Ve, P}.


declare module AC2: SConsis2_Adv {BP, H, HRO.RO, G}.
declare module AC3: SConsis3_Adv {BP, H, E, C, G}.

(* ** ASSUMPTIONS ** *)
(* ** start *)
  (* valid operator for ballots *)
  op validInd: pkey -> (ident * label * cipher) -> 
                     (h_in, h_out) map -> bool. 
  (* lossless *)
  (* -> for oracles *)
  axiom Gi_ll: islossless G.init.
  axiom Go_ll: islossless G.o.
  
  (* -> for validInd *)
  axiom Co_ll (H <: HOracle.ARO):
    islossless H.o =>
    islossless C(H).validInd.
   
  (* -> for proof system *)
  axiom Pp_ll (G <: GOracle.ARO): 
    islossless G.o =>
    islossless P(G).prove. 

  (* -> for encryption *)
  axiom Ek_ll (H <: HOracle.ARO): 
    islossless H.o =>
    islossless E(H).kgen.
  (* -> for strong consistency adversary *)
  axiom AC2_ll (O <: SCons_Oracle { AC2 }):
    islossless O.h       =>
    islossless O.g       =>
    islossless AC2(O).main.

  (* axiom for result distribution *)
  axiom Rho_weight (x: (ident * vote option) list):
    weight (Rho x) = 1%r. 

  (* axiom axiom for linking C.validInd to validInd operator *)
  axiom validInd_ax (gc: (glob C)) (pk: pkey) 
                  (b: ident * label * cipher):
    phoare[C(HRO.RO).validInd: 
          (glob C) = gc /\ arg = (b, pk) 
          ==>
          (glob C) = gc /\
          res = validInd pk b HRO.RO.m] = 1%r.

(* ** end *)

(* extract procedure *)
module CE(E: Scheme, H: HOracle.ARO)={
  proc extract(b: (ident * label * cipher), sk: skey): (ident * vote option) = {
    var v;
    v <@ E(H).dec(sk,b.`2, b.`3);
    return (b.`1, v);
  }
}.

(*# lemma consistency part 1,
          break correctness of encryption used for the VotingScheme *)
lemma consis1(id: ident, v: vote, l: label) &m: 
   Pr[SConsis1(MV(E,P,Ve,C), CE(E), H, G).main(id,v, l) @ &m: res]  >=
   Pr[PKEvf.Correctness(E, H).main(v,l) @ &m: res].
proof.
  byequiv(_: ={glob E, glob H}/\ 
             arg{1}.`1 = arg{2}.`2 /\ 
             arg{2}.`3 = arg{1}.`2 ==> _ )=>//.
  proc.
  inline *.
  wp; call (_: ={glob H}).
    by sim.
  wp; call (_: ={glob H}).
    by sim.
  wp; while{2} (0<=i0{2} <= nr{2})
              (nr{2} - i0{2}); progress.
      by auto; progress; smt.
  call(_: ={glob H}).
  auto.
  call{2} Gi_ll.
  call(_: true).
  by auto; progress; smt.
qed.

(*# lemma consistency part 3,
          result consistency: *) 
equiv consis3 &m:
    SConsis3_L(MV(E, P, Ve, C), C, AC3, H, G).main ~ 
    SConsis3_R(MV(E, P, Ve, C), CE(E), C, AC3, H, G).main
    : ={glob H, glob G, glob E, glob C, glob AC3} ==> ={res}. 
proof.
  proc.
  seq 10 11: ( ={glob E, glob H, BP.pk, BP.sk, bb, r, ev}/\
               ub{2} = []).
    wp; while (={ glob E, glob C, glob H, i, bb, BP.pk, ev}).
      sp; wp.
      if; auto.
      call(_: ={ glob H}).
        by sim.
      by auto.
    call(_: ={glob E, glob H, glob C, glob G, BP.pk, BP.sk, BP.uL}).
      by sim.
      by sim.
    call(_: ={glob E, glob H, BP.uL}).
      by sim.
    call(_: true); call(_: true). 
    by auto. 

  inline SConsis3_L(MV(E, P, Ve, C), C, AC3, H, G).V.tally.
  if=>//=.
  wp; call{1} (Pp_ll G Go_ll); auto.
  inline CE(E, H).extract.
  while ( ={ glob E, glob H} /\
          i0{1} = i{2}/\ bb0{1} = bb{2}/\
          sk{1} = BP.sk{2} /\
          ubb{1} = ub{2}).
    wp; call (_: = {glob H}).
      by sim. 
    by auto; progress. 
  by auto.
qed.

(*# lemma consistency part 2,
          valid => validInd *)
lemma consis2 &m: 
  Pr[SConsis2(MV(E, P, Ve, C), C, AC2, HRO.RO, G).main() @ &m: res] = 1%r.
proof.
  byphoare=>//.
  proc.
  inline SConsis2(MV(E, P, Ve, C), C, AC2, HRO.RO, G).V.valid.
  seq 15: (b0 = b/\ pk = BP.pk)=>//.
    while{2} (0 <= i <= size bb0)
             ( size bb0 - i); progress.
      by auto; progress; smt.
    auto.
    progress. 
    call{1} ( AC2_ll (<: SConsis2(MV(E, P, Ve, C), C, AC2, HRO.RO, G).O) _ _).
    + by apply HRO.RO_o_ll. 
    + by apply Go_ll.
    inline SConsis2(MV(E, P, Ve, C), C, AC2, HRO.RO, G).V.setup.
    wp; while{1} (0 <= i0 <= nr)
             (nr - i0); progress.
      by auto; progress; smt.
    call{1} (Ek_ll HRO.RO HRO.RO_o_ll).
    auto; call{1} Gi_ll. 
    call{1} (HRO.RO_init_ll _ _ ) ; first 2 by smt.
    by auto; progress; smt. 
   
    if; progress.
      exists* (glob C), BP.pk, b; elim* =>gc pk bv. 
      call{1} (validInd_ax gc pk bv); wp.
      call{1} (validInd_ax gc pk bv). 
      by auto; progress; smt.
    exists* (glob C), BP.pk, b; elim* =>gc pk bv. 
    call{1} (validInd_ax gc pk bv); wp.
    call{1} (validInd_ax gc pk bv).
    by auto; progress; smt.

  hoare; progress. 
  while (true).
    by auto.
  wp.
  call(_: true).
  + by conseq HRO.RO_o_ll. 
  + by conseq Go_ll.
  inline *.
  wp; while(true).
    by auto.
  call(_: true).
  by auto; call(_: true).
qed.

end section StrongConsistency.

(* ---------------------------------------------------------------------- *)
(* Strong Correctness  *)
section StrongCorrectness.
require import FSet.

declare module E : Scheme        
                   { BS, BP, BSC, BSCorr, HRO.RO}.
declare module S : Simulator 
                   { BSC, BSCorr, BP, BS, HRO.RO, E}.
declare module Ve: Verifier
                   { BS, BP, BSCorr, HRO.RO, E, S}.
declare module Pe : Prover
                   { BS, BP, BSCorr, HRO.RO, E, S, Ve}.
declare module C: ValidInd       
                   { BS, BP, BSC, BSCorr, HRO.RO, E, S, Ve, Pe}.

(* ** ASSUMPTIONS ** *)
(* ** start *)
  (* at least 2 distinct votes *)
  const v_def_0: vote.
  const v_def_1: vote.
  axiom v_distinct: v_def_0 <> v_def_1.

  (* encryption always implies validInd true *)
  axiom enc_to_validInd (pk: pkey) (id: ident) (v: vote) (l : label):
    equiv[ E(HRO.RO).enc ~ E(HRO.RO).enc: 
          ={glob HRO.RO, glob E, arg} /\ arg{1} = (pk,l,v)
         ==> ={res, glob E, glob HRO.RO} /\
          validInd pk (id, l, res{1}) HRO.RO.m{1}].

  (* axiom for linking C.validInd to validInd operator *)
  axiom validInd_ax (gc: (glob C)) (pk: pkey) 
                  (b: ident * label * cipher):
    phoare[C(HRO.RO).validInd: 
            (glob C) = gc /\ arg = (b, pk) 
            ==>
            (glob C) = gc /\ 
            res = validInd pk b HRO.RO.m] = 1%r.
  (* axiom for transforming an encryption into decryption (one-sided) *)
  axiom Eenc_decL (ge: (glob E)) (sk2: skey) (pk2: pkey)(l2: label) (p2: vote): 
    (pk2 = extractPk sk2) =>
    phoare [E(HRO.RO).enc : 
          (glob E) = ge /\ arg=(pk2, l2, p2) 
          ==> 
          (glob E) = ge /\
          Some p2 = dec_cipher sk2 l2 res HRO.RO.m ]= 1%r.

  (* axiom for transforming an encryption into decryption (two-sided) *)
  axiom Eenc_dec (sk2: skey) (pk2: pkey) (l2: label) (p2: vote): 
    (pk2 = extractPk sk2) =>
    equiv [E(HRO.RO).enc ~ E(HRO.RO).enc : 
          ={glob HRO.RO, glob E, arg} /\ arg{1}=( pk2, l2, p2)
          ==> 
          ={glob HRO.RO, glob E,  res} /\ 
          Some p2 = dec_cipher sk2 l2 res{1} HRO.RO.m{1}].

  (* axiom for linking E.dec to dec_cipher operator *)
  axiom Edec_Odec (ge: (glob E)) (sk2: skey)
                (l2: label) (c2: cipher):
    phoare [E(HRO.RO).dec:  
           (glob E) =ge /\ arg = (sk2, l2, c2) 
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
              (V<: VotingScheme{AS}) (O <: SCorr_Oracle {AS}):
    islossless O.h => 
    islossless O.g => 
    islossless O.test =>
    islossless AS(V,O).main.
(* ** end *)

(* Oracle that does a membership test for a freshly generated ciphertext and label 
   with respect to list of ciphertexts *)
module type Coll_Oracle ={
  proc mem_test(v: vote, lbl: label option, cL: (cipher * label) list): unit
}.

(* Membership oracle *)
module Coll_Oracle(E: Scheme, H: HOracle.ARO) ={
  proc mem_test(v: vote, l: label option, cL: (cipher * label) list): unit={
    var c;
    if (BSC.qt < 1){   
      if (size cL < n + k){
        if(l <> None){
          c <@ E(H).enc(BSC.pk, oget l, v);
          if(!BSC.valid){
            BSC.valid <- mem cL (c, oget l);      
          }
        }
      }
      BSC.qt <- BSC.qt + 1;
    }
  }
}.
 
(* Adversary for the collision on a fresh created ciphertext 
   with a list of existing ones *)
module type Coll_Adv (MO: Coll_Oracle) ={
  proc main(pk: pkey): unit 
}.

(* Experiment for the membership test *)
module MemCheck(E: Scheme, H: HOracle.Oracle, AC: Coll_Adv) ={
  module MO = Coll_Oracle(E,H)

  proc main(): bool ={
    var sk;

    BSC.valid <- false;
    BSC.qt <- 0;
    H.init();
    (BSC.pk, sk) <@ E(H).kgen();
    AC(MO).main(BSC.pk);
    return BSC.valid;
  }
}.

(* Membership adversary created from a strong correctness adversary *)
module Bmem(V: VotingScheme, AS: SCorr_Adv, G: GOracle.Oracle, 
            H: HOracle.Oracle, MO: Coll_Oracle)={
  module O = {
    proc h    = H.o
    proc g    = G.o
    proc test(id: ident, v: vote, bb: (ident * label * cipher) list ): unit ={
      var l, cL, i, b;

      cL <- [];
      i <- 0;
      l <- BSC.uL.[id];
      while(i < size bb){
        b <- oget (onth bb i);
        cL <- cL ++ [(b.`3, b.`2)];
        i <- i + 1;
      }
      MO.mem_test(v, l, cL);   
    }
  }(* end O *)

  module AS = AS(O)
  proc main(pk: pkey) ={
    var i, id;
    BSC.uL <- empty;
    G.init();                                                                                  
    i <- 0;
    while (i < part) {             
      id <$ d_ids;                              
      BSC.uL.[id] <- Flabel id;                           
      i <- i + 1;                                  
    } 
    AS.main(pk, BSC.uL);
  }
}.
  
(* lemma to show reduction from strong correctness experiment 
         to membership check experiment for minivoting *)
local lemma scorr_to_mem (AS <: SCorr_Adv' { E, Pe, Ve, C, HRO.RO, BSC} ) 
                         (G <: GOracle.Oracle { BS, BP, BSC, BSCorr, 
                                 HRO.RO, E, Pe, Ve, C, AS}) &m:
  Pr[SCorr(MV(E, Pe, Ve, C), 
           AS(MV(E, Pe, Ve, C)), HRO.RO, G).main() @ &m: BSC.valid ] =
  Pr[MemCheck(E, HRO.RO, 
              Bmem(MV(E, Pe, Ve, C), 
                   AS(MV(E, Pe, Ve, C)), G, HRO.RO)).main() @ &m: BSC.valid].
proof.
  byequiv(_: ={glob AS, glob G, glob E} ==> _ ) =>//=.
  proc.
  inline Bmem(MV(E, Pe, Ve, C), AS(MV(E, Pe, Ve, C)), G, HRO.RO, 
              MemCheck(E, HRO.RO, Bmem(MV(E, Pe, Ve, C),
                                       AS(MV(E, Pe, Ve, C)), G, HRO.RO)).MO).main.
  call(_: ={ glob HRO.RO, glob G, glob E, BSC.valid, BSC.qt, BSC.uL, BSC.pk}/\
          BSC.qt{1} <= 1). 
       
  + by proc. 
  + by proc (={glob HRO.RO, glob E, BSC.valid, BSC.qt, BSC.uL, BSC.pk} /\
            BSC.qt{1} <= 1) =>//=. 
  + proc.
    inline Coll_Oracle(E, HRO.RO).mem_test.
    sp.
    seq 0 1: (l{2} = BSC.uL{2}.[id{2}] /\ 
                ={id, v, bb, BSC.qt, BSC.valid, BSC.uL,
                  BSC.pk, glob G, glob E, glob HRO.RO} /\
                cL{2} = map (fun (b: ident * label * cipher) 
                              => (b.`3, b.`2)) bb{2} /\
                BSC.qt{1} <= 1).
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
      seq 17 1: (l{1} = BSC.uL{1}.[id{1}] /\
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
                 ={id, v, bb, BSC.qt, BSC.valid, glob E, 
                   BSC.uL, BSC.pk, glob G, glob HRO.RO} /\
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
                  (!ev1{1} <=> forall id, 
                            !mem bb0{1} (id, l0{1}, c{1}))).
        wp; sp.
        while{1}(0 <= i{1} <= size bb0{1} /\
                 (!ev1{1} <=> forall id, 
                             !mem (take i{1} bb0{1}) (id, b0{1}.`2, b0{1}.`3)))
                (size bb0{1} - i{1}); progress.
          auto; progress.                 
          + by smt.  + by smt. 
          + have Hm: 0<= i{hr} < size bb0{hr} by done.
            rewrite (take_nth witness) 1: Hm //; rewrite mem_rcons in_cons. 
            by smt.
          + have Hm: 0<= i{hr} < size bb0{hr} by done.
            move : H4; rewrite (take_nth witness) 1: Hm //; move => H4.
            cut Hx:= H4 (nth witness bb0{hr} i{hr}).`1.
            by smt.
          + by smt. + by smt. + by smt.
          + have Hm: 0<= i{hr} < size bb0{hr} by done.
            move: H3; rewrite H1; move => H3. 
            have Hx: exists (id : ident), 
                       mem (take i{hr} bb0{hr}) (id, b0{hr}.`2, b0{hr}.`3)
              by smt.
            move : Hx; elim => id Hx. 
            rewrite nforall //=; rewrite (take_nth witness) 1: Hm //.
            exists id.
            rewrite mem_rcons in_cons. 
            by smt.
          + by smt.

       wp; exists* BSC.pk{1}, id{1}, v0{1}, l0{1};
         elim* => pk1 id1 v01 l01.
       call{1} (enc_to_validInd pk1 id1 v01 l01). 
       by auto; progress; smt.
       
          
       wp; exists* (glob C){1}, BSC.pk{1}, b{1}; elim* => gc pk1 b1.
       call{1} (validInd_ax gc pk1 b1).
       auto; progress. 
       + rewrite H3 H4 mapP eq_iff -nnot H5 //=. 
         have ->: (! (forall (idx : ident), 
                     ! mem bb{2} (idx, oget BSC.uL{2}.[id{2}], c{2}))) <=>
                  exists idx, mem bb{2} (idx, oget BSC.uL{2}.[id{2}], c{2}) 
           by smt.
         progress.
         + by exists (idx, oget BSC.uL{2}.[id{2}], c{2}).
         - by exists x.`1; rewrite H8; smt.   
       + by smt.  + by smt.

    by auto; progress; smt.
    
  inline SCorr(MV(E, Pe, Ve, C), AS(MV(E, Pe, Ve, C)), HRO.RO, G).V.setup.
  wp; while (={i}/\ nr{1} =part /\ uL{1} = BSC.uL{2}).
    by auto.
  swap{1} 9 -4.
  wp; call (_: true). 
  wp; call (_: ={glob HRO.RO}). 
  call (_: true ==> ={glob HRO.RO}).
    by sim.
  by auto.
qed.

(* IND-1-CCA adversary that is constructed from a adv that 
       finds a membership collision *)
module INDB(AC: Coll_Adv, IO: Ind1CCA_Oracles) ={
  module O = {
    proc mem_test(v: vote, l: label option, cL: (cipher * label) list): unit={
      var c, mL, cmL, i, m, v', cl;
      if (BSC.qt < 1){   
        if (size cL < n + k){
          if(l <> None){
            (* extract encryptions of v *)
            mL  <@ IO.dec(cL);
            cmL <-[];
            i <- 0;
            while (i < size cL){
              m <- oget (onth mL i);
              cl <- oget (onth cL i);
              if( m = Some v){
                cmL <- cmL ++ [cl];
              }
              i <- i + 1;
            }
          
            (* generate new v' *)
            if (v = v_def_0){
              v' <- v_def_1;
            }else{
              v' <- v_def_0;
            }
          
            if (l <> None){
              (* encrypt left or right *)
              c <@ IO.enc(oget l, v, v');

              (* if c in encryptions of m, then return true (= mem check) 
                else false ( = non mem check) *)
              if(!BSC.valid){
                BSC.valid <- mem cmL (c, oget l);      
              }
            }
          }
        }
        BSC.qt <- BSC.qt + 1;
      }
    }
  }

  proc main(pk: pkey): bool ={
    BSC.valid <- false;
    BSC.qt <- 0;
    AC(O).main(pk);
    return BSC.valid;
  }
}.


(* Lemma equivalence for IND1CCA-L and Mem-test *)
lemma mem_to_ind (AS <: SCorr_Adv' { E, Pe, Ve, C, HRO.RO, BSC, BS} ) 
                 (G  <: GOracle.Oracle { BS, BP, BSC, BSCorr, 
                         HRO.RO, E, Pe, Ve, C, AS}) &m:
  Pr[MemCheck(E, HRO.RO, 
              Bmem(MV(E, Pe, Ve, C), 
                   AS(MV(E, Pe, Ve, C)), G, HRO.RO)).main() @ &m: BSC.valid] =
  Pr[Ind1CCA(E,
             INDB(Bmem(MV(E, Pe, Ve, C), 
                       AS(MV(E, Pe, Ve, C)), G, HRO.RO)),
             HRO.RO,Left).main()  @ &m: res /\  size BS.encL <= 1].
proof.
  byequiv(_: ={glob AS, glob E, glob G} ==> _ ) =>//=. 
  proc.
  
  inline Bmem(MV(E, Pe, Ve, C), AS(MV(E, Pe, Ve, C)), G, HRO.RO, 
              MemCheck(E, HRO.RO, 
                       Bmem(MV(E, Pe, Ve, C), 
                            AS(MV(E, Pe, Ve, C)), G, HRO.RO)).MO).main
    Ind1CCA(E, 
            INDB(Bmem(MV(E, Pe, Ve, C), 
                      AS(MV(E, Pe, Ve, C)), G, HRO.RO)), HRO.RO, Left).A.main
    Bmem(MV(E, Pe, Ve, C), AS(MV(E, Pe, Ve, C)), G, HRO.RO, 
         INDB(Bmem(MV(E, Pe, Ve, C), AS(MV(E, Pe, Ve, C)), G, HRO.RO), 
              Ind1CCA_Oracles(E, HRO.RO, Left)).O).main.
  wp. 
  call (_: ={glob HRO.RO, glob G, glob E, BSC.valid, BSC.qt, BSC.uL}/\
             BS.pk{2} =extractPk BS.sk{2} /\
             BSC.pk{1} = BS.pk{2} /\
             (BSC.qt{2} < 1 => !BS.decQueried{2} /\ BS.encL{2} = []) /\
             size BS.encL{2} <= BSC.qt{2} /\
             0 <= BSC.qt{2} <= 1).
  + by proc. 
  + have Go_ll2: equiv [ G.o ~ G.o: ={arg, glob G} ==> ={res, glob G}] 
      by  proc true; first 2 by progress.  
    conseq Go_ll2 ; first 2 by progress.
  + proc.
    inline Coll_Oracle(E, HRO.RO).mem_test
      INDB(Bmem(MV(E, Pe, Ve, C), AS(MV(E, Pe, Ve, C)), G, HRO.RO), 
           Ind1CCA_Oracles(E, HRO.RO, Left)).O.mem_test.
    inline *. 
    seq 7 7: ( ={id, v, bb, v0, l0, cL, cL0, glob HRO.RO, 
                 glob G, glob E, BSC.valid, BSC.qt, BSC.uL} /\
               v0{1} = v{1} /\ l0{1} = l{1} /\
               cL0{1} = cL{1}/\
               (BSC.qt{2} < 1 => !BS.decQueried{2} /\ BS.encL{2} = [])/\
               0 <= BSC.qt{2} <= 1 /\
               size BS.encL{2} <= BSC.qt{2} /\
               BS.pk{2} =extractPk BS.sk{2} /\
               BSC.pk{1} = BS.pk{2} /\
               cL{2} = map (fun (b: ident * label * cipher) 
                              => (b.`3, b.`2)) bb{2}).
      wp; while (={i,bb, cL} /\ 0 <= i{2} /\
                 cL{2} = map (fun (b: ident * label * cipher) 
                              => (b.`3, b.`2)) (take i{2} bb{2})).
        auto; progress. 
        + smt.
        + have Hm: 0<= i{2} < size bb{2} by done.
          rewrite (take_nth witness) 1: Hm //. 
          by smt.
    auto; progress; smt.
    if =>//=. 
    if =>//=; last by auto; progress; smt.  
    if =>//=; last by auto; progress; smt.
    swap{2} 9 -8.
    seq 0 1: (={id, v, bb, v0, l0, cL, cL0, glob HRO.RO, 
                glob G, glob E, BSC.valid, BSC.qt, BSC.uL}/\
              v0{1} = v{1} /\
              l0{1} = l{1} /\
              cL0{1} = cL{1} /\
              (BSC.qt{2} < 1 => 
                !BS.decQueried{2} /\ BS.encL{2} = []) /\
              0 <= BSC.qt{2} <= 1 /\
              size BS.encL{2} <= BSC.qt{2} /\
              BS.pk{2} = extractPk BS.sk{2} /\
              BSC.pk{1} = BS.pk{2} /\
              cL{2} = map (fun (b0 : ident * label * cipher) 
                           => (b0.`3, b0.`2)) bb{2} /\
              BSC.qt{1} < 1 /\
              size cL0{1} < n + k/\
              l0{1} <> None).
      by auto; progress; smt. (* getting rid of the other vote*)     

    seq 0 8: (={id, v, bb, v0, l0, cL, cL0, glob G, 
                glob HRO.RO, glob E, BSC.valid, 
                BSC.qt, BSC.uL} /\
               v0{1} = v{1} /\
               l0{1} = l{1} /\
               cL0{1} = cL{1} /\
               (cL{2} = map (fun (b0 : ident * label * cipher) 
                            => (b0.`3, b0.`2)) bb{2}) /\
               BSC.qt{1} < 1 /\
               size cL0{1} < n + k /\
               l0{1} <> None /\
               BS.pk{2} =extractPk BS.sk{2} /\
               BSC.pk{1} = BS.pk{2} /\
               0 <= BSC.qt{2} <= 1 /\
               size BS.encL{2} <= BSC.qt{2} /\
               BSC.qt{2} <= 1/\
               cmL{2} = filter 
                        (fun (cl: cipher * label) => 
                             dec_cipher BS.sk{2} cl.`2 cl.`1 HRO.RO.m{2} 
                             = Some v0{2}) 
                        cL0{2} /\
               mL{2} = map (fun (cl : cipher * label) =>
                      dec_cipher BS.sk{2} cl.`2 cl.`1 HRO.RO.m{2}) cL0{2}).
     while{2} (0 <= i0{2} /\
               cmL{2} = filter (fun (cl: cipher * label) => 
                                dec_cipher BS.sk{2} cl.`2 cl.`1 HRO.RO.m{2} 
                                = Some v0{2}) 
                        (take i0{2} cL0{2}) /\
               mL{2} = map (fun (cl : cipher * label) =>
                      dec_cipher BS.sk{2} cl.`2 cl.`1 HRO.RO.m{2}) cL0{2})
              (size cL0{2} - i0{2}). 
       progress.
       auto; progress. 
       + smt. 
       + rewrite (take_nth witness); first by smt. 
         rewrite filter_rcons //=. 
         have ->: (dec_cipher BS.sk{hr} (nth witness cL0{hr} i0{hr}).`2
                                        (nth witness cL0{hr} i0{hr}).`1 
                              HRO.RO.m{hr} =
                   Some v0{hr}) = true by smt.
         progress. 
         by smt.
       + by smt. + by smt.
       + rewrite (take_nth witness); first by smt. 
         rewrite filter_rcons //=.
         by smt.
       + by smt.
    wp; sp.
    rcondt{2} 1. progress. auto; progress. smt. 
    exists * (glob E){2} ; elim* => ge.
    wp; while{2} (0 <= i1{2}/\ ge = (glob E){2} /\
                  (mL0{2} = map (fun (cl : cipher * label) =>
                                dec_cipher BS.sk{2} cl.`2 cl.`1 HRO.RO.m{2}) 
                            (take i1{2} cL1{2}))/\
                  BS.encL{2} = [])
                 (size cL1{2} - i1{2}); progress.
    wp; sp.
    exists* BS.sk, l1, c0; 
      elim * => sk2 l2 c2. 
    call{1} (Edec_Odec ge sk2 l2 c2).
    auto; progress. 
    + by smt. 
    + rewrite (take_nth witness); first by smt.
      by smt.
    + by smt.      
    by auto; progress; smt. 

    rcondt{2} 1; first progress; smt.
    wp; sp.
    exists* (glob E){2}, BS.pk{2}, BS.sk{2}, l2{2}, p{2}; 
      elim * => ge pk1 sk1 l1 v1. 
      pose kp:=  (pk1= extractPk sk1).
      cut em_kp: kp \/ !kp by smt. 
      elim em_kp. 
      + move => h. 
        call{1} (Eenc_dec sk1 pk1 l1 v1 h).  
        by auto; progress; smt.
      - move => h.    
        conseq(_: _ ==> !(BS.pk{2} =extractPk BS.sk{2})); 
          progress. 
        call{1} (Ee_ll HRO.RO HRO.RO_o_ll).
        call{2} (Ee_ll HRO.RO HRO.RO_o_ll).
        by auto; progress; smt.
    
  wp; while (={i, BSC.uL}).
    by auto; progress; smt.
  wp; call(_: true); wp.
  call{1} (Ekgen_extractPk HRO.RO).
  call (_: true ==> ={glob HRO.RO}).
    by sim.
  by auto; progress; smt.
qed.

(* Lemma for IND1CCA-R = 0 *)
lemma ind_to_zero (AS <: SCorr_Adv' { E, Pe, Ve, C, HRO.RO, BSC, BS} )
                  (G  <: GOracle.Oracle { BS, BP, BSC, BSCorr, 
                                 HRO.RO, E, Pe, Ve, C, AS}) &m:
  islossless G.init =>
  islossless G.o =>
  Pr[Ind1CCA(E,
             INDB(Bmem(MV(E, Pe, Ve, C),
                       AS(MV(E, Pe, Ve, C)), G, HRO.RO)),
             HRO.RO,Right).main()  @ &m: res /\  size BS.encL <= 1] = 0%r.
proof.
  move => Gi_ll Go_ll.
  byphoare=>//=.
  proc.
  inline Ind1CCA(E, 
                 INDB(Bmem(MV(E, Pe, Ve, C), 
                           AS(MV(E, Pe, Ve, C)), G, HRO.RO)), 
                 HRO.RO, Right).A.main
         Bmem(MV(E, Pe, Ve, C), AS(MV(E, Pe, Ve, C)), G, HRO.RO, 
              INDB(Bmem(MV(E, Pe, Ve, C), AS(MV(E, Pe, Ve, C)), G, HRO.RO), 
                   Ind1CCA_Oracles(E, HRO.RO, Right)).O).main.
  wp.   
  phoare split ! 1%r 1%r =>//=. 
  (* goal 1: lossless *) 
    call (AC_ll AS (MV(E,Pe,Ve,C)) 
                (<:Bmem(MV(E, Pe, Ve, C), 
                        AS(MV(E, Pe, Ve, C)), G, HRO.RO, 
                        INDB(Bmem(MV(E, Pe, Ve, C), 
                                  AS(MV(E, Pe, Ve, C)), G, HRO.RO), 
                             Ind1CCA_Oracles(E, HRO.RO, Right)).O).O) _ _ _).
    + proc; auto.    
    + conseq Go_ll.   
    + proc.
      inline *.
      seq 7: (cL0 = cL /\ l0 = l /\ v0 = v/\ l = BSC.uL.[id])=>//=.
        wp; while{1} (true) (size bb - i).
          by auto; progress; smt.
        by auto; progress; smt.
      
        if =>//=.      
        if =>//=; last by auto. 
        if =>//=; last by auto. 
        sp; if =>//=. 
          rcondt 8; progress.
          + wp; while (true). 
              by auto; progress; smt.
            wp; while (true).
              by auto; progress; smt.
            by auto.
          wp; call (Ee_ll HRO.RO HRO.RO_o_ll).
          wp; while{1} (true) (size cL0 - i0); progress.
            by auto; progress; smt.
          wp; while{1} (true) (size cL1 - i1); progress.
            by wp; call (Ed_ll HRO.RO HRO.RO_o_ll); auto; progress; smt.
          by auto; progress; smt.

        rcondt 6; progress.
          + wp; while (true). 
              by auto; progress; smt.
            by auto.
        wp; call (Ee_ll HRO.RO HRO.RO_o_ll).
        wp; while{1} (true) (size cL0 - i0); progress.
          by auto; progress; smt.
        by auto; progress; smt.

      hoare =>//=.
      wp; while (true).
        by auto; progress.
      auto; progress.
    
    (* before AS.main *)
    while{1} (true) (part - i); progress.
      by auto; progress; smt.
    wp; call Gi_ll.
    wp; call (Ek_ll HRO.RO HRO.RO_o_ll).
    call (_: true). 
      while{1} (true) (card work); progress.
        by auto; progress; smt.
      by auto; progress; smt.
    by auto; progress; smt.

  (* goal 2: result *) 
  call (_:  BS.pk =extractPk BS.sk /\ 
            (BSC.qt < 1 => !BS.decQueried /\ BS.encL = []) /\
            size BS.encL <= BSC.qt /\
            0 <= BSC.qt <= 1 /\
            !BSC.valid).
  + exact (AC_ll AS).
  + proc; auto.
  + conseq Go_ll.
  + proc.
    seq 4: (l = BSC.uL.[id] /\ 
            cL = map (fun (b0 : ident * label * cipher) 
                           => (b0.`3, b0.`2)) bb /\
            BS.pk = extractPk BS.sk /\
            (BSC.qt < 1 => 
                !BS.decQueried /\ BS.encL = []) /\
            size BS.encL <= BSC.qt /\ 
            0 <= BSC.qt <= 1/\
            !BSC.valid) =>//=.
      (* first seq, goal 1 of 3 *) 
      while{1} ( 0 <= i <= size bb /\
                 (cL = map (fun (b0 : ident * label * cipher) 
                           => (b0.`3, b0.`2)) (take i bb)))
               (size bb - i); progress.
        by auto; progress; smt.
      by auto; progress; smt.

      (* first seq, goal 2 of 3 *)
      inline *; sp.
      if =>//=.
      if =>//=; last by auto; progress; smt.
      if =>//=; last by auto; progress; smt.
      sp; rcondt 1; progress.
        by auto; progress; smt.
      swap 7 -6.
     
      seq 1 :(cL1 = cL0 /\ i1 = 0 /\ mL0 = [] /\
             v0 = v /\ l0 = l /\ cL0 = cL /\
             l = BSC.uL.[id] /\
             cL = map (fun (b0 : ident * label * cipher) 
                       => (b0.`3, b0.`2)) bb /\
             BS.pk = extractPk BS.sk /\
             (BSC.qt < 1 => 
                 !BS.decQueried /\ BS.encL = []) /\
             size BS.encL <= BSC.qt /\
             0 <= BSC.qt <= 1 /\
             !BSC.valid /\
             BSC.qt < 1 /\
             size cL0 < n + k /\
             l0 <> None/\ v' <> v)=>//=.
        (* second seq, goal 1 of 3 *)
        by auto; progress; smt.    
        
        (* second seq, goal 2 of 3 *)
        seq 6: ( cL1 = cL0  /\ 
             v0 = v /\ l0 = l /\ cL0 = cL /\
             l = BSC.uL.[id] /\
             cL = map (fun (b0 : ident * label * cipher) 
                       => (b0.`3, b0.`2)) bb /\
             BS.pk = extractPk BS.sk /\
             size BS.encL <= BSC.qt /\
             0 <= BSC.qt <= 1 /\
             !BSC.valid /\
             BSC.qt < 1 /\
             size cL0 < n + k /\
             l0 <> None/\ v' <> v /\
             cmL = filter 
                        (fun (cl: cipher * label) => 
                             dec_cipher BS.sk cl.`2 cl.`1 HRO.RO.m 
                             = Some v0) 
                        cL0 /\
             mL = map (fun (cl : cipher * label) =>
                      dec_cipher BS.sk cl.`2 cl.`1 HRO.RO.m) cL0) =>//=.

          while{1} (0 <= i0 /\
                    cmL = filter (fun (cl: cipher * label) => 
                                dec_cipher BS.sk cl.`2 cl.`1 HRO.RO.m
                                = Some v0) 
                        (take i0 cL0) /\
                    mL = map (fun (cl : cipher * label) =>
                      dec_cipher BS.sk cl.`2 cl.`1 HRO.RO.m) cL0)
                   (size cL0 - i0); progress. 
            auto; progress. 
            + by smt. 
            + rewrite (take_nth witness); first by smt. 
              rewrite filter_rcons //=. 
              have ->: (dec_cipher BS.sk{hr} (nth witness cL0{hr} i0{hr}).`2
                                             (nth witness cL0{hr} i0{hr}).`1
                                   HRO.RO.m{hr} =
                   Some v0{hr}) = true by smt.
              simplify. 
              by smt.
            + by smt.
            + by smt.
            + rewrite (take_nth witness); first by smt. 
              rewrite filter_rcons //=.
              by smt.
            + by smt.
          wp; sp.
          exists * (glob E) ; elim* => ge.
          wp; while{1} (0 <= i1 /\ ge = (glob E) /\
                  (mL0 = map (fun (cl : cipher * label) =>
                      dec_cipher BS.sk cl.`2 cl.`1 HRO.RO.m) (take i1 cL1))/\
                  BS.encL = [])
                 (size cL1 - i1); progress.
            wp; sp.
            exists* BS.sk, l1, c0; 
              elim * => sk2 l2 c2. 
            call{1} (Edec_Odec ge sk2 l2 c2).
            auto; progress.
            + by smt.
            + rewrite (take_nth witness); first by smt.
              by smt.
            + by smt.

          by auto; progress; smt.

          rcondt 1; progress.
          sp; wp.          
          exists* (glob E), BS.pk, BS.sk, l2, p; 
            elim * => ge pk1 sk1 l1 v1. 
          pose kp:=  (pk1= extractPk sk1).
          cut em_kp: kp \/ !kp by smt. 
          elim em_kp. 
          + move => h. 
            call{1} (Eenc_decL ge sk1 pk1 l1 v1 h).  
            by auto; progress; smt.
          - move => h. 
            conseq(_: _ ==>  !(BS.pk =extractPk BS.sk)); 
              progress.
              case (!BSC.valid{hr}).
                by smt. 
              by smt.
            call{1} (Ee_ll HRO.RO HRO.RO_o_ll).
            by auto; progress; smt. 
     
      
          phoare split ! 1%r 1%r; progress.
            while{1} (true) (size cL0 - i0); progress.
              by auto; progress; smt.
            wp; while{1} (true) (size cL1 - i1); progress.
              wp; call {1} (Ed_ll HRO.RO HRO.RO_o_ll).
              by auto; progress; smt.
            by auto; progress; smt.

          while{1} (0 <= i0 /\
               cmL = filter (fun (cl: cipher * label) => 
                                dec_cipher BS.sk cl.`2 cl.`1 HRO.RO.m 
                                = Some v0) 
                        (take i0 cL0) /\
               mL = map (fun (cl : cipher * label) =>
                      dec_cipher BS.sk cl.`2 cl.`1 HRO.RO.m) cL0)
                  (size cL0 - i0); progress.
            auto; progress. 
            + by smt. 
            + rewrite (take_nth witness); first by smt. 
              rewrite filter_rcons //=. 
              have ->: (dec_cipher BS.sk{hr} (nth witness cL0{hr} i0{hr}).`2
                                             (nth witness cL0{hr} i0{hr}).`1 
                                   HRO.RO.m{hr} =
                       Some v0{hr}) = true by smt.
              simplify. 
              by smt.
            + by smt.
            + by smt.
            + rewrite (take_nth witness); first by smt. 
              rewrite filter_rcons //=.
              by smt.
            + by smt.
          wp; sp.
          exists * (glob E) ; elim* => ge.
          wp; while{1} (0 <= i1 /\ ge = (glob E) /\
                    (mL0 = map (fun (cl : cipher * label) =>
                               dec_cipher BS.sk cl.`2 cl.`1 HRO.RO.m) 
                           (take i1 cL1))/\
                           BS.encL = [])
                  (size cL1 - i1); progress.
            wp; sp.
            exists* BS.sk, l1, c0; 
              elim * => sk2 l2 c2. 
            call (Edec_Odec ge sk2 l2 c2).
            auto; progress. 
            + by smt. 
            + rewrite (take_nth witness); first by smt.
              by smt.
            + by smt.
     
        by auto; progress; smt.

     (* second seq, goal 3 of 3*) 
     hoare=>//=. 
     by auto; progress; smt.

    (* first seq, goal 3 of 3 *)
    hoare=>//=.
    while{1} ( 0<= i /\
               cL = map (fun (b0 : ident * label * cipher) 
                         => (b0.`3, b0.`2)) (take i bb)).
      by auto; progress; smt.
    by auto; progress; smt.
 
  (* before AS.main *)  
  wp; while{1} (true) (part - i).
      by auto; progress; smt.
  wp; call Gi_ll. progress.
  wp; call (Ekgen_extractPkL HRO.RO).
  inline *.
  while{1} (true) (card work); progress.
    by auto; progress; smt.
  by auto; progress; smt.
qed.

(* Lemma bounding strong correctness  *) 
lemma scorr (AS <: SCorr_Adv' { E, Pe, Ve, C, HRO.RO, BSC, BS}) 
            (G  <: GOracle.Oracle { BS, BP, BSC, BSCorr, HRO.RO, E, Pe, Ve, C, AS}) &m:
  islossless G.init =>
  islossless G.o =>
  Pr[SCorr(MV(E, Pe, Ve, C), 
           AS(MV(E,Pe,Ve,C)), HRO.RO, G).main() @ &m: BSC.valid ] = 
`|Pr[Ind1CCA(E,INDB(Bmem(MV(E, Pe, Ve, C), 
                         AS(MV(E, Pe, Ve, C)), G, HRO.RO)),
             HRO.RO,Left).main() @ &m: res /\  size BS.encL <= 1] -
  Pr[Ind1CCA(E,INDB(Bmem(MV(E, Pe, Ve, C), 
                         AS(MV(E, Pe, Ve, C)), G, HRO.RO)),
             HRO.RO,Right).main() @ &m: res /\  size BS.encL <= 1]|.
proof.  
  move => Gi_ll Go_ll. 
  rewrite (scorr_to_mem AS G &m).
  rewrite (mem_to_ind AS G &m).
  rewrite (ind_to_zero AS G &m Gi_ll Go_ll).
  by smt.
qed.

(* ---------------------------------------------------------------------- *)
(* actual proof with bscorr over bpriv_adv *)

declare module A: BPRIV_Adv { BSC, BS, BSCorr, BP, S, Pe, Ve, C, E, HRO.RO}.
(* need to use AS = BSCorr(MV(E,Pe,Ve,C),A, LR), and G as =S *)

  (*declare module LR: LorR {E}.*)
  local module BSCorr'(LR : LorR, V : VotingScheme, SO : SCorr_Oracle) 
             = BSCorr(V,A,LR,SO). 
  local module BSCorr''(E: Scheme, Pe: Prover, Ve: Verifier, 
                        C: ValidInd, LR: LorR, SO : SCorr_Oracle) 
             = BSCorr'(LR, MV(E,Pe,Ve,C), SO).

(* Lemma for the strong correctness in the BPRIV case *) 
lemma scorr_bpriv (LR<: LorR { BS, BP, BIND, BIND2, BSCorr, 
                         BSC, HRO.RO, A, C, E, Pe, Ve, S}) &m:
  Pr[SCorr (MV(E,Pe,Ve,C), BSCorr(MV(E,Pe,Ve,C),A, LR), HRO.RO, S).main() 
         @ &m: BSC.valid] = 
`|Pr[Ind1CCA(E,INDB(Bmem(MV(E, Pe, Ve, C), 
                         BSCorr(MV(E,Pe,Ve,C),A, LR), S, HRO.RO)),
             HRO.RO,Left).main()  @ &m: res /\  size BS.encL <= 1] -
  Pr[Ind1CCA(E,INDB(Bmem(MV(E, Pe, Ve, C), 
                         BSCorr(MV(E,Pe,Ve,C),A, LR), S, HRO.RO)),
             HRO.RO,Right).main() @ &m: res /\  size BS.encL <= 1]|. 
proof. 
  have ->: Pr[SCorr(MV(E,Pe,Ve,C), BSCorr(MV(E,Pe,Ve,C),A,LR),
                    HRO.RO,S).main() @ &m: BSC.valid]
         = Pr[SCorr(MV(E,Pe,Ve,C), BSCorr'(LR,MV(E,Pe,Ve,C)),
                    HRO.RO,S).main() @ &m: BSC.valid].
    by byequiv=> //=; sim.
  have ->: Pr[Ind1CCA(E, 
                      INDB(Bmem(MV(E, Pe, Ve, C), 
                                BSCorr(MV(E,Pe,Ve,C),A,LR),S,HRO.RO)),
                      HRO.RO, Left).main() @ &m : res /\ size BS.encL <= 1]
         = Pr[Ind1CCA(E, 
                      INDB(Bmem(MV(E, Pe, Ve, C), 
                                BSCorr'(LR,MV(E,Pe,Ve,C)),S,HRO.RO)),
                      HRO.RO, Left).main() @ &m : res /\ size BS.encL <= 1].
    by byequiv =>//=; sim.
  have ->: Pr[Ind1CCA(E, 
                      INDB(Bmem(MV(E, Pe, Ve, C), 
                                BSCorr(MV(E,Pe,Ve,C),A,LR),S,HRO.RO)),
                      HRO.RO, Right).main() @ &m: res /\ size BS.encL <= 1]
         = Pr[Ind1CCA(E, 
                      INDB(Bmem(MV(E, Pe, Ve, C), 
                                BSCorr'(LR,MV(E,Pe,Ve,C)),S,HRO.RO)),
                      HRO.RO, Right).main() @ &m: res /\ size BS.encL <= 1].
    by byequiv =>//=; sim. 
  
  by rewrite (scorr (BSCorr'(LR)) S &m Si_ll So_ll). 
qed.

end section StrongCorrectness.

