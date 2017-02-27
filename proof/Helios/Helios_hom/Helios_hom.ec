require import Option List Distr NewDistr.
require (*  *) PreHelios.
require (*  *) Bigop.
require import Distr Int FMap Real Pair Mu_mem. 
require import LeftOrRight.

(* basic types and operators used for the encryption scheme space *)
  type ident, fq.
  op Fq_zero: fq. (* zero element for addition *)
  op (+): fq -> fq -> fq. (* addition *)
  
  (* removes invalid elements *)
  op removeInvalid  (ubb: (ident * fq option) list) =
    with ubb = "[]"         => []
    with ubb = (::) idv ubb => if idv.`2 = None
                               then removeInvalid ubb
                               else (idv.`1, oget idv.`2) :: removeInvalid ubb.

  (* counting operator that does addition *)
  op Count (ubb: (ident * fq) list): fq =
    with ubb = "[]" => Fq_zero
    with ubb = (::) idv ubb =>  idv.`2 + (Count ubb).

  (* abstract policy *)
  op Policy['a]: (ident * 'a) list -> (ident * 'a) list.
  
  (* remove identities *)
  op rem_id (bb: (ident * 'a) list) = map snd bb.
 
  (* result function: count over Policy *)
  op Rho (x: (ident * fq option) list) = 
       MUnit.dunit (Count (Policy (removeInvalid x))).

  (* Helios-hom with a fixed Rho *) 
  clone export PreHelios as HH with
    type MV2.ident  <- ident,
    type MV2.result <- fq,
    type fq         <- fq,
    op Fq_zero      <- Fq_zero,
    op MV2.Rho      <- Rho.
  
  
  (* homomorphic property added to the abstract encryption scheme in IPKE*)
  op Add     : (h_cipher list) -> h_cipher option.
  axiom addC  (x y: fq)  : x + y = y + x.
  axiom addA  (x y z: fq): x + (y + z) = (x + y) + z.
  axiom add0f (x: fq)    : Fq_zero + x = x.

  clone Bigop as BigAdd with
    type       t   <- fq,
    op Support.idm <- Fq_zero,
    op Support.(+) <- (+)
    proof Support.Axioms.*.
    realize Support.Axioms.addmA. by apply addA.  qed.
    realize Support.Axioms.addmC. by apply addC.  qed.
    realize Support.Axioms.add0m. by apply add0f. qed.
    import BigAdd.

  (* ** Assumptions on the homomorphic property *)
  axiom hom_val (sk: skey) (clist: h_cipher list):
    (forall c, mem clist c => 
             decrypt sk c <> None) =>
    decrypt sk (oget (Add clist)) <> None.
  
  axiom hom_add (sk: skey) (clist: h_cipher list):
    (forall c, mem clist c => 
             decrypt sk c <> None) =>
    oget (decrypt sk (oget (Add clist))) = 
    BigAdd.big predT (fun (c: h_cipher) => 
                          oget (decrypt sk c)) clist.


(* ---------------------------------------------------------------------------------------------*)  
(* Helios-hom voting system *) 
module HeliosHom (Pe: PSpke.Prover, Ve: PSpke.Verifier, 
                  Pz: Prover,  Vz: Verifier, C: ValidInd,
                  H: HOracle.ARO,   G: GOracle.ARO)  = {

  proc setup  = MV(IPKE(Pe,Ve), Pz, Vz, C, H, G).setup
  proc valid  = MV(IPKE(Pe,Ve), Pz, Vz, C, H, G).valid
  proc vote   = MV(IPKE(Pe,Ve), Pz, Vz, C, H, G).vote
  proc verify = MV(IPKE(Pe,Ve), Pz, Vz, C, H, G).verify 

  (* tally algorithm *)
  proc tally(bb: (ident * label * cipher) list, sk: skey): fq * prf = {
    var  b, i, pbb, sbb, ev, c, cL, pk, r, pi, r';

    sbb <- [];
    i   <- 0;
    pk  <- extractPk sk;

    (* keep only valid ballots *)
    while (i < size bb){
      b <- oget (onth bb i);
      ev<@ Ve(H).verify(to_statement pk b.`2 b.`3.`1, b.`3.`2);
      if(ev){
        (* keep only id and h_cipher*)
        sbb <- sbb ++ [(b.`1,b.`3.`1)];
      }
      i <- i + 1;
    }
    
    (* apply policy *)
    cL <- rem_id (Policy sbb);
    (* compute ciphertext by homomorphic addition *)
    c  <- Add cL;

    (* compute result *)
    r <- Fq_zero;
    if (cL <> []){
      r' <- decrypt sk (oget c);
      if(r'<> None){(* decryption doesn't fail *)
        r <- oget r';
      } 
    }

    (* create proof *)
    pbb  <- Publish (bb);
    pi   <@ Pz(G).prove((pk, pbb, r), (sk, bb));

    return (r, pi);
  }

  (* intermediary tally algorithm, between Helios-hom.tally and MV.tally *)
  proc tally'(bb: (ident * label * cipher) list, sk: skey): fq * prf = {
    var ubb, b, i, m, pbb, sbb, ev, c, id, sanbb, pk, r, pi;

    ubb <- [];
    sbb <- [];
    i   <- 0;
    pk  <- extractPk sk;
    (* keep only valid ballots *)
    while(i < size bb){
      b <- oget (onth bb i);
      ev<@ Ve(H).verify(to_statement pk b.`2 b.`3.`1, b.`3.`2);
      if(ev){
        (* keep only id and h_cipher*)
        sbb <- sbb ++ [(b.`1, b.`3.`1)];
      }
      i <- i + 1;
    }
 
    (* decrypt ballots *)
    i <- 0;
    while( i < size sbb){
      (id,c)  <- oget (onth sbb i);
      m   <- decrypt sk c;
      ubb <- ubb ++ [(id, oget m)];
      i  <- i + 1;
    }
    
    (* apply policy *)
    sanbb <- Policy ubb;
    (* compute result *)
    r     <- Count sanbb;

    (* create proof *)
    pbb   <- Publish (bb);
    pi    <@ Pz(G).prove((pk, pbb, r), (sk, bb));

    return (r, pi);
  }
}.

(* ---------------------------------------------------------------------------------*)
section HeliosHom_homomorphicAddition.

declare module C : ValidInd       {BP, HRO.RO, BSC}. 
declare module Pe: PSpke.Prover   {C, BP, HRO.RO, SCorr_Oracle, BSC }.
declare module Ve: PSpke.Verifier {C, Pe, BP, HRO.RO}.

declare module Pz: Prover         {C, Pe, Ve, BP, HRO.RO }.
declare module Vz: Verifier       {C, Pe, Ve, Pz, BP, HRO.RO }.
declare module G : GOracle.Oracle {C, Pe, Ve, Pz, Vz, BP, HRO.RO, BSC, SCorr_Oracle}.
declare module S : Simulator      {C, Pe, Ve, Pz, Vz, G, BP, HRO.RO, BSC}.
declare module A : BPRIV_Adv      {C, Pe, Ve, Pz, Vz, G, S, HRO.RO, BP }. 

(* ** ASSUMPTIONS ** *)
(* ** start *)
  (* axiom on commutativity of policy and decryption *)
  axiom san_tallymap (sbb: (ident * h_cipher) list) (sk: skey):
    let f = (fun (b : ident * h_cipher) =>
                (b.`1, (oget (decrypt sk b.`2)))) in
    Policy (map f sbb) = map f (Policy sbb).

  (* axiom on membership of policy *)
  axiom san_mem (sbb: (ident * h_cipher) list) (b: ident * h_cipher):
    mem (Policy sbb) b => mem sbb b.

  (* axiom on transforming Ve.verify in verify operator *)
  axiom Verify_to_verify (gv: (glob Ve)) (s: h_stm) (p: h_prf):
    phoare[Ve(HRO.RO).verify: (glob Ve) = gv  /\ arg = (s, p)
         ==>
         (glob Ve) = gv /\ 
         res = verify s p HRO.RO.m] = 1%r.
(* ** end *)

(* removing invalid plaintext is the same as removing ballots based on verify check *)
local lemma rmap_mapmapf (bb: (ident * label * cipher) list) (sk: skey) (ro: (h_in,h_out) map):
  removeInvalid
    (map (fun (b : ident * label * cipher) =>
          if verify (to_statement (extractPk sk) b.`2 b.`3.`1) b.`3.`2 ro  
          then (b.`1, (decrypt sk b.`3.`1))
          else (b.`1, None)) 
     bb) =
  map (fun (b : ident * h_cipher) =>
       (b.`1,  (oget (decrypt sk b.`2))))
  (map (fun (b : ident * label * cipher) => (b.`1, b.`3.`1))
   (filter (fun (b : ident * label * cipher) =>
            verify (to_statement (extractPk sk) b.`2 b.`3.`1) b.`3.`2 ro) 
            bb)).
proof.
  elim bb =>//= x l Hr. 
  cut T:= verify_validDec sk (x.`2, x.`3) ro.  
  by smt.
qed.

(* counting plaintext list is the same as decrypting a homomorphic addition *) 
local lemma fg (sbb: (ident * h_cipher) list) (sk: skey):
  (forall b, mem sbb b => 
      (decrypt sk b.`2 <> None)) =>
  Count (map (fun (b : ident * h_cipher) =>
                  (b.`1, (oget (decrypt sk b.`2))))
         sbb)  =
  oget (decrypt sk (oget (Add (rem_id sbb)))).
proof.
  elim sbb =>//=. smt.
  move => x l Hxl Hb.  
  rewrite hom_add; first by smt. 
  have ->: (rem_id (x :: l)) = x.`2 ::(rem_id l) by rewrite /rem_id //=.
  rewrite BigAdd.big_cons /predT //=. 
  rewrite Hxl; first by smt. 
  rewrite hom_add /predT; first by smt. 
  by done.
qed.

(* lemma for result distribution *) 
local lemma Rho_weight (x: (ident * fq option) list):
  weight (Rho x)= 1%r. 
proof.
  by smt.
qed. 

(* equivalence between MV.tally and HeliosHom.tally' *)
local equiv MV_Helios_tally1:
  MV(IPKE(Pe,Ve),Pz,Vz,C, HRO.RO, G).tally ~ HeliosHom(Pe, Ve, Pz, Vz, C, HRO.RO, G).tally'
  : ={glob HRO.RO, glob G, glob Pz, glob Pe, glob Ve, arg}  
      ==>
    ={res, glob HRO.RO, glob G, glob Pz, glob Pe, glob Ve}.
proof.
  proc.
  swap{2} 1 4. 
  swap{1} 6 -3.
  seq 0 4: (={sk, bb, glob HRO.RO, glob G,
              glob Pz, glob Pe, glob Ve}/\
            pk{2}=extractPk sk{2} /\
            sbb{2} = map (fun (b: ident * label * cipher) =>
                              (b.`1, b.`3.`1))
                     (filter (fun (b: ident * label * cipher) =>
                              verify (to_statement pk{2} b.`2 b.`3.`1) 
                                     b.`3.`2 HRO.RO.m{2})
                              bb{2})).
    exists* (glob Ve){2}; elim * => gv.
    while{2} (0 <= i{2} <= size bb{2} /\ (glob Ve){2}=gv /\
              sbb{2} = map (fun (b: ident * label* cipher) =>
                           (b.`1, b.`3.`1))
                     (filter (fun (b: ident * label* cipher) =>
                              verify (to_statement pk{2} b.`2 b.`3.`1) 
                                     b.`3.`2 HRO.RO.m{2})
                           (take i{2} bb{2})))
             (size bb{2} - i{2}); progress.
      exists* pk{hr}, bb{hr}, i{hr}; elim * => pk2 bb2 i2.
      inline *; wp; sp.
      pose b2:= oget (onth bb2 i2). 
      call{1} (Verify_to_verify gv (to_statement pk2 b2.`2 b2.`3.`1) b2.`3.`2).
      auto; progress.
      + by smt. + by smt. 
      + have Hm: 0<= i{hr} < size bb{hr} by done.
        rewrite (take_nth witness) 1: Hm // filter_rcons. 
        by smt.
      + by smt. + by smt. + by smt. 
      + have Hm: 0<= i{hr} < size bb{hr} by done.
        rewrite (take_nth witness) 1: Hm // filter_rcons. 
        by smt.
      + by smt. 
    by auto; progress; smt.
  
  call (_: ={glob G}); first by sim.
  wp; while{2} (0 <= i{2} <= size sbb{2} /\
                  sbb{2} = map (fun (b: ident * label * cipher) =>
                                    (b.`1, b.`3.`1))
                          (filter (fun (b: ident * label * cipher) =>
                                       verify (to_statement pk{2} b.`2 b.`3.`1) 
                                              b.`3.`2 HRO.RO.m{2})
                                   bb{2}) /\
                  ubb{2} = map (fun (b: ident * h_cipher) => 
                                    (b.`1, (oget (decrypt sk{2} b.`2))))
                           (take i{2} sbb{2}))
                  (size sbb{2} - i{2}); progress.
    auto; progress.
    + by smt. + by smt. 
    + rewrite (take_nth witness); first by smt. 
      rewrite // -cats1.
      by smt.
    + by smt. 

  exists* (glob Ve){1}; elim * => gv.
  auto.
  while{1} (0 <= i{1} <= size bb{1} /\ (glob Ve){1}= gv /\ 
            ubb{1} = map (fun (b: ident * label * cipher) => 
                              if (verify (to_statement (extractPk sk{1}) b.`2 b.`3.`1) 
                                         b.`3.`2 HRO.RO.m{1})
                              then (b.`1, decrypt sk{1} b.`3.`1)
                              else (b.`1, None))
                     (take i{1} bb{1}))
           (size bb{1} - i{1}); progress.
    exists* sk{hr}, bb{hr}, i{hr}; elim * => sk1 bb1 i1.
    inline *; wp; sp.
    pose b1:= oget (onth bb1 i1). 
    call{1} (Verify_to_verify gv (to_statement (extractPk sk1) b1.`2 b1.`3.`1) b1.`3.`2).
    auto; progress.
    + by smt. + by smt. + by smt. + by smt. 
    + have Hm: 0<= i{hr} < size bb{hr} by done.
      rewrite (take_nth witness) 1: Hm // -cats1 map_cat. 
      by smt.
    + by smt. + by smt. + by smt.
    + have Hm: 0<= i{hr} < size bb{hr} by done.
      rewrite (take_nth witness) 1: Hm // -cats1 map_cat.  
      by smt.
    + by smt.

  auto; progress.  
  + by smt. + by smt. + by smt. 
  + by smt. + by smt. + by smt.  + by smt.  
  + rewrite /Rho.
    have ->>: i_L= size bb{2} by smt.
    move: H2 H3.
    have ->: (take (size bb{2}) bb{2}) = bb{2} by smt.
    have ->: (take i_R (map (fun (b : ident * label * cipher) => (b.`1, b.`3.`1))
                          (filter (fun (b : ident * label * cipher) =>
                                   verify (to_statement (extractPk sk{2}) b.`2 b.`3.`1)
                                          b.`3.`2 HRO.RO.m{2}) bb{2}))) =
               (map (fun (b : ident * label * cipher) => (b.`1, b.`3.`1))
                (filter (fun (b : ident * label * cipher) =>
                         verify (to_statement (extractPk sk{2}) b.`2 b.`3.`1)
                         b.`3.`2 HRO.RO.m{2}) bb{2})) by smt.
    rewrite /Rho rmap_mapmapf.
    pose xx:= (map 
               (fun (b : ident * h_cipher) => (b.`1, oget (decrypt sk{2} b.`2)))
               (map (fun (b : ident * label * cipher) => (b.`1, b.`3.`1))
                    (filter (fun (b : ident * label * cipher) =>
                             verify (to_statement (extractPk sk{2}) b.`2 b.`3.`1) 
                                     b.`3.`2 HRO.RO.m{2}) 
                             bb{2}))). 
    move => H2 H3. 
    by smt. 
qed.

(* equivalence between HeliosHom.tally' and HeliosHom.tally *)
local equiv MV_Helios_tally2:
  HeliosHom(Pe, Ve, Pz, Vz, C, HRO.RO, G).tally' ~ 
  HeliosHom(Pe, Ve, Pz, Vz, C, HRO.RO, G).tally
  : ={glob HRO.RO, glob G, glob Pz, glob Pe, glob Ve, arg}
      ==>
    ={res, glob HRO.RO, glob G, glob Pz, glob Pe, glob Ve}.
proof.
  proc.
  swap{1} 1 4. 
  seq 4 4: (={glob HRO.RO, glob G, glob Pz, 
              glob Pe, glob Ve, bb, sk, pk, sbb} /\
            pk{1} = extractPk sk{1}/\
            (forall b, mem sbb{2} b => 
                 (decrypt sk{2} b.`2 <> None))).
    while( ={ i, bb, sbb, pk, sk, glob Ve, glob HRO.RO, sk}/\ 
           0 <= i{2} /\ pk{1} = extractPk sk{1} /\  
              (forall b, mem sbb{2} b => 
                 (decrypt sk{2} b.`2 <> None))).
      inline *; sp; wp.
      exists* (glob Ve){1}, sk{1}, bb{1}, i{1}; elim * => gv sk1 bb1 i1.
      pose b1:= oget (onth bb1 i1). 
      call{1} (Verify_to_verify gv (to_statement (extractPk sk1) b1.`2 b1.`3.`1) b1.`3.`2).
      call{2} (Verify_to_verify gv (to_statement (extractPk sk1) b1.`2 b1.`3.`1) b1.`3.`2).
      auto; progress.
      + by smt.
      + move: H8. 
        rewrite cats1 mem_rcons //=.
        move => H8. 
        cut T:= verify_validDec sk{2} (b1.`2, b1.`3) HRO.RO.m{2} _; first by rewrite //=.
        by smt.
      + by smt.
    by auto.

  call(_: ={glob G}); first by sim. 
  wp; while{1} (0 <= i{1} <= size sbb{1} /\
              ubb{1} = map (fun (b: ident * h_cipher) => 
                            (b.`1, (oget (decrypt sk{1} b.`2))))
                      (take i{1} sbb{1}))
              (size sbb{1} - i{1}); progress.
    by auto; progress; smt.

  auto; progress.
  + by smt. + by smt. + by smt.
  + have ->>: i_L = size sbb{2} by smt.
    rewrite take_size.
    cut Ht:= (fg (Policy sbb{2}) sk{2} _). 
      move => b Hs.  
      cut t:= san_mem sbb{2} b Hs.
      by smt.
    cut := san_tallymap sbb{2} sk{2}. 
    simplify; move => Hf.
    by rewrite Hf Ht. 
  + cut t:= hom_val sk{2} (rem_id (Policy sbb{2})) _; first by smt. 
    by smt. 
  + have ->>: i_L = size sbb{2} by smt.
    rewrite take_size. 
    cut :=(san_tallymap sbb{2} sk{2}).
    simplify.
    pose f:= (fun (b : ident * h_cipher) =>
             (b.`1, oget (decrypt sk{2} b.`2))). 
    rewrite //=. 
    have ->: (Policy sbb{2}) = [] by smt.
    smt.
qed.

(* equivalence between MV.tally and HeliosHom.tally *)
equiv MV_HA_tally:
  MV(IPKE(Pe,Ve),Pz,Vz,C, HRO.RO, G).tally ~ HeliosHom(Pe, Ve, Pz, Vz, C, HRO.RO, G).tally
  : ={glob HRO.RO, glob G, glob Pz, glob Pe, glob Ve, arg}  
      ==>
    ={res, glob HRO.RO, glob G, glob Pz, glob Pe, glob Ve}.
proof.

  transitivity HeliosHom(Pe, Ve, Pz, Vz, C, HRO.RO, G).tally' 
  (={glob HRO.RO, glob G, glob Pz, glob Pe, glob Ve, arg} ==> 
   ={res, glob HRO.RO, glob G, glob Pz, glob Pe, glob Ve})
  (={glob HRO.RO, glob G, glob Pz, glob Pe, glob Ve, arg} ==> 
   ={res, glob HRO.RO, glob G, glob Pz, glob Pe, glob Ve})=>//=. 
  by progress; smt.
  by apply (MV_Helios_tally1).
  by apply (MV_Helios_tally2).
qed.
end section HeliosHom_homomorphicAddition.

(* -----------------------------------------------------------------------------*)
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
                                   SCorr_Oracle}.
declare module S : Simulator      {C, Pe, Ve, Pz, Vz, G, Rz, BS, BP, BSC, BSCorr, HRO.RO, BSC, BPS,
                                   BPRIV_SB, BIND2, BIND, PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv}.

(* adversary models *)
declare module A : BPRIV_Adv      {C, Pe, Ve, Pz, Vz, Rz, G, S, HRO.RO, BP, BS, BSCorr, BSC, BPS,
                                   PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv, BPRIV_SB, BIND, BIND2 }.
declare module AC2: SConsis2_Adv {BP, HRO.RO, G, C}.
declare module AC3: SConsis3_Adv {BP, HRO.RO, Pe, Ve, Pz, C, G}.
 
(* ** ASSUMPTIONS ** *)
(* ** start *)
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

local lemma MV_HA_bpriv &m:
  `|Pr[BPRIV_L(MV(IPKE(Pe, Ve), Pz, Vz, C), A, HRO.RO, G).main() @ &m : res] -
    Pr[BPRIV_R(MV(IPKE(Pe, Ve), Pz, Vz, C), A, HRO.RO, G, S).main() @ &m :res]|
= `|Pr[BPRIV_L(HeliosHom(Pe, Ve, Pz, Vz, C), A, HRO.RO, G).main() @ &m : res] -
    Pr[BPRIV_R(HeliosHom(Pe, Ve, Pz, Vz, C), A, HRO.RO, G, S).main() @ &m :res]|.
proof.
  have ->: Pr[BPRIV_L(MV(IPKE(Pe, Ve), Pz, Vz, C), A, HRO.RO, G).main() @ &m : res] =
           Pr[BPRIV_L(HeliosHom(Pe, Ve, Pz, Vz, C), A, HRO.RO, G).main() @ &m : res].
    byequiv (_: ={glob A, glob G, glob Pz, 
                  glob Pe, glob Ve, glob C} ==> _ ) =>//=. 
    proc.
    call (_: ={glob HRO.RO, glob G, glob Pz, 
               BP.bb1, BP.bb0, BP.sk, BP.uL, BP.pk});
      [1..3: by sim]. 
    call (MV_HA_tally C Pe Ve Pz Vz G S A san_tallymap 
                      san_mem Verify_to_verify).
    call (_: ={glob HRO.RO, glob G, glob Pz, 
               glob Pe, glob Ve, glob C,
               BP.bb1, BP.bb0, BP.sk, BP.uL, 
               BP.pk, BP.qVo, BP.qCa});
      [1..5: by sim]. 
    call(_: ={glob HRO.RO, BP.uL}); first
      by sim.
    call(_: true).
    call(_: true ==> ={glob HRO.RO}).
      by sim.
    by auto.

  have ->: Pr[BPRIV_R(MV(IPKE(Pe, Ve), Pz, Vz, C), A, HRO.RO, G, S).main() @ &m : res] =
           Pr[BPRIV_R(HeliosHom(Pe, Ve, Pz, Vz, C), A, HRO.RO, G, S).main() @ &m : res].
    byequiv (_: ={glob A, glob G, glob Pz, glob S,
                  glob Pe, glob Ve, glob C} ==> _ ) =>//=.
    proc.
    call (_: ={glob HRO.RO, glob G, glob Pz, glob S,
               BP.bb1, BP.bb0, BP.sk, BP.uL, BP.pk});
      [1..3: by sim]. 
    call(_: true).
    wp; call (MV_HA_tally C Pe Ve Pz Vz G S A san_tallymap 
                          san_mem Verify_to_verify).
    call (_: ={glob HRO.RO, glob G, glob Pz, glob S,
               glob Pe, glob Ve, glob C,
               BP.bb1, BP.bb0, BP.sk, BP.uL, 
               BP.pk, BP.qVo, BP.qCa});
      [1..5: by sim].
    call(_: ={glob S}); first by sim. 
    call(_: true); call(_: true).
    call(_: true ==> ={glob HRO.RO}).
      by sim. 
    by auto; progress; smt.

  by done.   
qed.

(* Lemma bounding bpriv *)
lemma bpriv &m: 
  `|Pr[BPRIV_L(HeliosHom(Pe, Ve, Pz, Vz, C), A, HRO.RO, G).main() @ &m : res] -
    Pr[BPRIV_R(HeliosHom(Pe, Ve, Pz, Vz, C), A, HRO.RO, G, S).main() @ &m :res]|
<=
    Pr[VFR(IPKE(Pe, Ve), BVFR(MV(IPKE(Pe, Ve), Pz, Vz, C), A), 
           Rz(IPKE(Pe,Ve)), HRO.RO, G).main() @ &m : res] +
    Pr[VFR(IPKE(Pe, Ve), BVFR(MV(IPKE(Pe, Ve), Pz, Vz, C), A), 
           Rz(IPKE(Pe,Ve)), HRO.RO, S).main() @ &m : res] +
  `|Pr[ZK_L(Rz(IPKE(Pe,Ve),HRO.RO), Pz, 
            BZK(IPKE(Pe, Ve), Pz, C, Vz, A, HRO.RO), G).main() @ &m : res] -
    Pr[ZK_R(Rz(IPKE(Pe,Ve),HRO.RO), S , 
            BZK(IPKE(Pe, Ve), Pz, C, Vz, A, HRO.RO)).main() @ &m : res]| +
n%r *
    Pr[SCorr(MV(IPKE(Pe, Ve), Pz, Vz, C), 
             BSCorr(MV(IPKE(Pe, Ve), Pz, Vz, C), A, Left), 
             HRO.RO, S).main() @ &m : BSC.valid] +
n%r *
    Pr[SCorr(MV(IPKE(Pe, Ve), Pz, Vz, C), 
             BSCorr(MV(IPKE(Pe, Ve), Pz, Vz, C), A, Right), 
             HRO.RO, S).main() @ &m : BSC.valid] +
n%r *
  `|Pr[Ind1CCA(IPKE(Pe, Ve), 
               WrapAdv(BIND(MV(IPKE(Pe, Ve), Pz, Vz, C), A, S), 
                       IPKE(Pe, Ve), HRO.RO), 
               HRO.RO, Left).main() @ &m : 
               res /\ WrapAdv.l <= n /\ size BS.encL <= 1] -
    Pr[Ind1CCA(IPKE(Pe, Ve), 
               WrapAdv(BIND(MV(IPKE(Pe, Ve), Pz, Vz, C), A, S), 
                       IPKE(Pe, Ve), HRO.RO), 
               HRO.RO, Right).main() @ &m : 
               res /\ WrapAdv.l <= n /\ size BS.encL <= 1]|.
proof.
  rewrite -(MV_HA_bpriv &m).
  by rewrite (bpriv G S Vz Pz Rz C A Ve Pe Verify_to_verify 
                    LPKE_prover_keepstate Prover_to_verify 
                    Prover_to_verify_left validInd_ax
                    relConstraint _ Gi_ll Go_ll Pp_ll Vv_ll 
                    Si_ll So_ll Sp_ll A1_ll A2_ll C_ll 
                    Vval_ll Vvot_ll Pe_ll Ve_ll &m); first by smt. 
qed.
 
(* Lemma bounding strong consistency part 1 *)
lemma consis1(id: ident, v: plain, l: label) &m: 
   Pr[SConsis1(HeliosHom(Pe, Ve, Pz, Vz, C), 
               CE(IPKE(Pe,Ve)), HRO.RO, G).main(id,v, l) @ &m: res]  
   >=
   Pr[PKEvf.Correctness(IPKE(Pe,Ve), HRO.RO).main(v,l) @ &m: res].
proof.
  have ->: Pr[SConsis1(HeliosHom(Pe, Ve, Pz, Vz, C), 
                       CE(IPKE(Pe,Ve)), HRO.RO, G).main(id,v, l) @ &m: res] =
           Pr[SConsis1(MV(IPKE(Pe,Ve), Pz, Vz, C), 
                       CE(IPKE(Pe,Ve)), HRO.RO, G).main(id,v, l) @ &m: res].  
    by byequiv =>//=; sim. 
  by rewrite (consis1 HRO.RO G S Vz Pz Ve Pe C AC2 AC3
                      Gi_ll Go_ll C_ll Pp_ll AC2_ll _ validInd_ax id v l &m); first by smt. 
qed.  

(* Lemma bounding strong consistency part 2 *)
lemma consis2 &m:
  Pr[SConsis2(HeliosHom(Pe, Ve, Pz, Vz, C), C, AC2, HRO.RO, G).main() @ &m: res] = 1%r.
proof. 
  have ->: Pr[SConsis2(HeliosHom(Pe, Ve, Pz, Vz, C), C, AC2, HRO.RO, G).main() @ &m: res]=
           Pr[SConsis2(MV(IPKE(Pe,Ve), Pz, Vz, C), C, AC2, HRO.RO, G).main() @ &m: res].
    byequiv =>//=. 
    proc; wp.
    call(_: ={glob HRO.RO}); first by sim. 
    call(_: ={BP.uL, BP.pk, glob C, glob HRO.RO}); first
      by sim. 
    call(_: ={glob G, glob HRO.RO}); 
      first 2 by sim. 
    call(_: ={glob HRO.RO}); first by sim.
    call(_: true). 
    call (_: true ==> ={glob HRO.RO}); first
      by sim.
    by auto; progress; smt.

  by rewrite (consis2 HRO.RO G S Vz Pz Ve Pe C AC2 AC3
                      Gi_ll Go_ll C_ll Pp_ll AC2_ll _ validInd_ax &m); first by smt.
qed.

(* left side of strong consistency part 3 *)
local equiv consis_tally_L :
  SConsis3_L(HeliosHom(Pe, Ve, Pz, Vz, C), C, AC3, HRO.RO, G).V.tally ~ 
  SConsis3_L(MV(IPKE(Pe, Ve), Pz, Vz, C), C, AC3, HRO.RO, G).V.tally
   : ={glob HRO.RO, glob G, glob Pz, glob Pe, glob Ve, arg}  
      ==>
    ={res, glob HRO.RO, glob G, glob Pz, glob Pe, glob Ve}.
proof.
  symmetry =>//=.
  conseq (_: ={glob HRO.RO, glob G, glob Pz, glob Pe, glob Ve, arg} ==>
   ={res, glob HRO.RO, glob G, glob Pz, glob Pe, glob Ve})=>//=. 
  by rewrite (MV_HA_tally C Pe Ve Pz Vz G S A san_tallymap 
                          san_mem Verify_to_verify).   
qed. 

(* Lemma bounding strong consistency part 3 *)
equiv consis3 &m:
    SConsis3_L(HeliosHom(Pe, Ve, Pz, Vz, C), C, AC3, HRO.RO, G).main ~ 
    SConsis3_R(HeliosHom(Pe, Ve, Pz, Vz, C), CE(IPKE(Pe,Ve)), C, AC3, HRO.RO, G).main
    : ={glob HRO.RO, glob G, glob IPKE(Pe,Ve), glob C, glob Pz, glob AC3} ==> ={res}.
proof.
  (* Because of the tally from HeliosHom to MV, glob Pz (used to create the proof) 
     is needed *)
  transitivity SConsis3_L(MV(IPKE(Pe,Ve), Pz, Vz, C), C, AC3, HRO.RO, G).main 
  (={glob HRO.RO, glob G, glob IPKE(Pe,Ve), glob C, glob Pz, glob AC3} ==> 
   ={res})
  (={glob HRO.RO, glob G, glob IPKE(Pe,Ve), glob C, glob Pz, glob AC3} ==> 
   ={res})=>//=. 

  + by progress; smt.

  + proc. 
    seq 10 10: (={ev, r, bb, BP.sk, glob HRO.RO, glob C,
                glob G, glob Pz, glob IPKE(Pe, Ve)})=>//=.
      by sim. 
    if; auto. 
    by call (consis_tally_L).

  transitivity SConsis3_R(MV(IPKE(Pe,Ve), Pz, Vz, C), 
                          CE(IPKE(Pe,Ve)), C, AC3, HRO.RO, G).main 
  (={glob HRO.RO, glob G, glob IPKE(Pe,Ve), glob C, glob Pz, glob AC3} ==> 
   ={res})
  (={glob HRO.RO, glob G, glob IPKE(Pe,Ve), glob C, glob Pz, glob AC3} ==> 
   ={res})=>//=. 

  + by progress; smt.

  + conseq (_: ={glob HRO.RO, glob G, glob IPKE(Pe, Ve), glob C, glob AC3} ==> _)=>//=.
    by rewrite (consis3 HRO.RO G S Vz Pz Ve Pe C AC2 AC3
                      Gi_ll Go_ll C_ll Pp_ll AC2_ll _ validInd_ax &m); first by smt. 
  - by sim. 
qed.

(* Lemma bounding strong correctness, general version *)
lemma scorr_bound (AS <: SCorr_Adv' { IPKE(Pe,Ve), Pz, Vz, C, HRO.RO, BSC, BS}) 
                  (G  <: GOracle.Oracle { BS, BP, BSC, BSCorr, HRO.RO, IPKE(Pe,Ve), Pz, Vz, C, AS}) &m:
  islossless G.init =>
  islossless G.o =>
  Pr[SCorr(HeliosHom(Pe, Ve, Pz, Vz, C), AS(HeliosHom(Pe, Ve, Pz, Vz, C)), 
           HRO.RO, G).main() @ &m: BSC.valid ] = 
`|Pr[Ind1CCA(IPKE(Pe,Ve), 
             INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, C), 
                       AS(MV(IPKE(Pe,Ve), Pz, Vz, C)), G, HRO.RO)), 
             HRO.RO,Left).main()  @ &m: res /\  size BS.encL <= 1] -
  Pr[Ind1CCA(IPKE(Pe,Ve), 
             INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, C), 
                       AS(MV(IPKE(Pe,Ve), Pz, Vz, C)), G, HRO.RO)),
             HRO.RO,Right).main()  @ &m: res /\  size BS.encL <= 1]|.
proof. 
  have ->:Pr[SCorr(HeliosHom(Pe, Ve, Pz, Vz, C), 
                   AS(HeliosHom(Pe, Ve, Pz, Vz, C)), HRO.RO, G).main() @ &m: BSC.valid ] =
          Pr[SCorr(MV(IPKE(Pe,Ve), Pz, Vz, C), 
                   AS(MV(IPKE(Pe,Ve),Pz,Vz,C)), HRO.RO, G).main() @ &m: BSC.valid ].
    by byequiv =>//=; sim. print scorr.
  by exact (scorr Pe Ve C S Vz Pz A Pe_ll Ve_ll AC_ll So_ll Si_ll v_distinct
                      Prover_to_verify Prover_to_verify_left Verify_to_verify 
                      enc_to_validInd validInd_ax AS G &m).
qed.

(* Lemma bounding strong correctness, for bpriv adversary *)
lemma scorr_bpriv (LR<: LorR { BS, BP, BIND, BIND2, BSCorr, BSC, HRO.RO, 
                        A, Ve, C, Vz, Pz, Pe, S}) &m:
  Pr[SCorr (HeliosHom(Pe, Ve, Pz, Vz, C), 
            BSCorr(HeliosHom(Pe, Ve, Pz, Vz, C),A, LR), HRO.RO, S).main() @ &m: BSC.valid] = 
`|Pr[Ind1CCA(IPKE(Pe,Ve),INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, C), 
                                    BSCorr(MV(IPKE(Pe,Ve),Pz,Vz, C),A, LR), S, HRO.RO)),
         HRO.RO,Left).main() @ &m: res /\  size BS.encL <= 1] -
  Pr[Ind1CCA(IPKE(Pe,Ve),INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, C),
                                    BSCorr(MV(IPKE(Pe,Ve),Pz,Vz, C),A, LR), S, HRO.RO)),
         HRO.RO,Right).main() @ &m: res /\  size BS.encL <= 1]|.
proof.
  have ->: Pr[SCorr (HeliosHom(Pe, Ve, Pz, Vz, C), 
                     BSCorr(HeliosHom(Pe, Ve, Pz, Vz, C),A, LR), HRO.RO, S).main() @ &m: BSC.valid]=
           Pr[SCorr (MV(IPKE(Pe,Ve),Pz,Vz, C), 
                     BSCorr(MV(IPKE(Pe,Ve),Pz,Vz, C),A, LR), HRO.RO, S).main() @ &m: BSC.valid].
    by byequiv =>//=; sim. 
  by rewrite (scorr_bpriv Pe Ve C S Vz Pz A Pe_ll Ve_ll AC_ll So_ll Si_ll v_distinct
                      Prover_to_verify Prover_to_verify_left Verify_to_verify 
                      enc_to_validInd validInd_ax LR &m). 
qed.
end section Security.
