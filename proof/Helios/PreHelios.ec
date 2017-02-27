require import Int List Option Distr FMap Pair Real FSet Mu_mem CyclicGroup.
require import LeftOrRight. 
require (*  *) MiniVoting_Weed.

  (* basic types and operators used for the encryption scheme space *)
  type fq.           (* plaintext *)
  op Fq_zero: fq.    (* zero element for addition *)
  const v_def_0: fq. (* 2 distinct elements *)
  const v_def_1: fq.
  (* distribution over plaintexts *)
  op dfq : fq distr.
  (* assumption over distribution *)
  axiom dfq_ll: is_lossless dfq.
  axiom supp_def: forall (s:fq), in_supp s dfq.

(* Labelled Public-Key Encryption Scheme =
   abstract encryption scheme + abstract proof system *)
 
  (* ** abstract  encryption scheme *)
    (* Types and operators *)
    type h_cipher, skey, pkey.
    type plain = fq.
    op dskey: skey distr. 
    axiom dskey_ll: is_lossless dskey.

    (* encryption scheme algorithms *)
    op extractPk: skey -> pkey.
    op decrypt  : skey -> h_cipher -> fq option.
    op encrypt  : pkey -> plain -> t -> h_cipher.

  (* ** abstract Proof System *)
    (* Types and operators *)
    type label, h_stm, h_wit, h_prf, h_in, h_out, h_data.
    type cipher = h_cipher * h_prf * h_data.
    op hash: h_cipher -> h_prf -> h_data.

    (* distribution over the output of the hash function *)
    op dh_out: h_out distr.

    (* abstract operators *)
    op verify      : h_stm -> h_prf -> (h_in, h_out) map -> bool.
    op to_statement: pkey -> label -> h_cipher -> h_stm.
    op to_witness  : plain -> t -> h_wit.

    clone export ProofSystem as PSpke with
      type stm   <- h_stm,
      type wit   <- h_wit,
      type prf   <- h_prf,
      type g_in  <- h_in,
      type g_out <- h_out,
      op dout    <- dh_out
      proof *.

  (* ** Assumptions on the labelled public-key encryption scheme *)
    (* the zk proof is verified to true, 
       then the decryption will succeed (<> None) *)
    axiom verify_validDec (sk: skey) (b: label * cipher) (ro: (h_in,h_out) map) :
      verify (to_statement (extractPk sk) b.`1 b.`2.`1) b.`2.`2 ro =>
        (decrypt sk b.`2.`1 <> None).

    (* correctness property based on small values *)
    axiom correctness (sk: skey) (p: fq) (r: t):
      decrypt sk (encrypt (extractPk sk) p r ) = Some p.

 
  (* FIXME: remove the bound, use n from export *)
  op n : { int | 0 < n } as n_pos.     

  (* Import encryption scheme *)
  clone export LPKE as Ipke with
    type label  <- label,
    type plain  <- plain,
    type cipher <- cipher,
    type pkey   <- pkey,
    type skey   <- skey,
    type h_in   <- h_in,
    type h_out  <- h_out,
    op   dout   <- dh_out,
    op   n      <- n
    proof *.
    realize n_pos. by apply n_pos. qed.
  
  (* Labelled Public-Key Encryption Scheme  *)
  module IPKE(P: Prover, Ve: Verifier, O:ARO) = {
    proc kgen(): pkey * skey ={
      var sk; 
      sk <$dskey; 
    return (extractPk sk, sk);
    }

    proc enc(pk: pkey, lbl: label, p: plain) : cipher ={
      var r, c, pi;

      r <$ FDistr.dt; 
      c <- encrypt pk p r;
      pi<@ P(O).prove((to_statement pk lbl c), (to_witness p r) );

      return (c, pi, hash c pi);
    }

    proc dec(sk: skey, lbl: label, c: cipher) : plain option = {
      var ev, m;

      m <- None; 
      ev <@ Ve(O).verify((to_statement (extractPk sk) lbl c.`1), c.`2);
      if (ev){
        m <- decrypt sk c.`1;
      }
      return m;   
    }
    
  }.

(* ---------------------------------------------------------------------- *)
(* Minivoting with IPKE as an encryption scheme *)

(* decryption operator *)
op dec_cipher (sk: skey, lbl: label, c: cipher, ro: (h_in, h_out) map) =
    let s = to_statement (extractPk sk) lbl c.`1 in 
    if(verify s c.`2 ro) 
      then (decrypt sk c.`1)
      else None.

clone export MiniVoting_Weed as MV2 with
  type label  <- label,  
  type vote   <- plain,  
  (* use LPKE types *)
  type cipher   <- cipher, 
  type pkey     <- pkey,   
  type skey     <- skey,   
  type h_in     <- h_in,   
  type h_out    <- h_out,   
  op dh_out     <- dh_out, 
  op n          <- n,            
  op dec_cipher <- dec_cipher,        
  op extractPk  <- extractPk,
  op v_def_0    <- v_def_0,
  op v_def_1    <- v_def_1
  proof n_pos.
  realize n_pos. by smt. qed. 

  (* needed for bpriv*)
  export PSvf. 

(* BPRIV PROPERTY *)
(* --------------------------------------------------------------------------*)
section BPRIV.

declare module G : GOracle.Oracle 
                   { BP, BS, BPS, BIND, HRO.RO}.
declare module S : Simulator 
                   { BP, BS, BPS, BSC, BIND, HRO.RO, G, BSCorr,
                     BPRIV_SB, BIND2, PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv}.
declare module Vz: Verifier
                   { BP, BS, BPS, BSC, BSCorr, BIND, HRO.RO, G, S}.
declare module Pz : Prover
                   { BP, BS, BPS, BSC, BSCorr, BIND, HRO.RO, G, S, Vz}.
declare module Rz : VotingRelation'
                   { BPS, BP, BS, G, S, Pz, Vz, HRO.RO}.
declare module C: ValidInd       
                   { BP, BS, BPS, BSC, BSCorr, BIND, HRO.RO, G, S, Vz, Pz, Rz,
                     BPRIV_SB, BIND2, PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv}.
declare module A: BPRIV_Adv        
                  { BP, BS, BPS, BSC, BSCorr, HRO.RO, G, S, Vz, Pz, Rz, C, 
                    PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv, BPRIV_SB, BIND, BIND2}. 

(* this are needed for the LPKE scheme *)
declare module Ve: PSpke.Verifier
                  { BP, BS, BPS, BSC, BSCorr, BIND, HRO.RO, G, S, Vz, Pz, Rz, C, A,
                    PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv, BPRIV_SB, BIND2}.
declare module Pe: PSpke.Prover
                  { BP, BS, BPS, BSC, BSCorr, BIND, HRO.RO, G, S, Vz, Pz, Rz, C, A, Ve,
                    PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv, BPRIV_SB, BIND2}.

(* ** ASSUMPTIONS ** *)
(* ** start *)
  (* axiom for linking Ve.verify to verify operator *)
  axiom Verify_to_verify (gv: (glob Ve)) (s: h_stm) (p: h_prf):
    phoare[Ve(HRO.RO).verify: (glob Ve) = gv /\ arg = (s, p)
         ==>
         (glob Ve) = gv /\
         res = verify s p HRO.RO.m] = 1%r.

  (* axiom for state of prover in IPKE *)
  axiom LPKE_prover_keepstate (gp: (glob Pe)) (H<: HOracle.ARO):
    phoare[Pe(H).prove: 
          (glob Pe) = gp ==> (glob Pe) = gp] = 1%r.

  (* axiom for transforming a proof in a verification (two-sided) *)
  axiom Prover_to_verify (s: h_stm) (w: h_wit):
    equiv[Pe(HRO.RO).prove ~ Pe(HRO.RO).prove: 
         ={glob HRO.RO, glob Pe, arg} /\ arg{1} = (s, w)
         ==>
         ={glob HRO.RO, glob Pe, res} /\
         verify s res{1} HRO.RO.m{1}].

  (* axiom for transforming a proof in a verification (two-sided) *)
  axiom Prover_to_verify_left (gp: (glob Pe)) (s: h_stm) (w: h_wit):
    phoare[Pe(HRO.RO).prove: 
          (glob Pe) = gp /\ arg = (s, w)
          ==>
          (glob Pe) = gp /\ verify s res HRO.RO.m]= 1%r.

  (* axiom for linking C.validInd to validInd operator *)
  axiom validInd_ax (gc: (glob C)) (pk: pkey) (b: ident * label * cipher):
    phoare[C(HRO.RO).validInd: 
            (glob C) = gc /\ arg = (b, pk) 
            ==>
            (glob C) = gc /\ res = validInd pk b HRO.RO.m] = 1%r.

  (* axiom on a voting relation that does not 
     change the eager random oracle state *)
  axiom relConstraint (gh : (glob HRO.RO)):
    phoare[Rz(IPKE(Pe,Ve),HRO.RO).main : 
          (glob HRO.RO) = gh ==> (glob HRO.RO) = gh] = 1%r.

  (* axiom for result distribution *)
  axiom Rho_weight (x: (ident * plain option) list):
    weight (Rho x)= 1%r.
  
  (* lossless *)
  (* -> random oracle *)
  axiom Gi_ll: islossless G.init. 
  axiom Go_ll: islossless G.o.

  (* -> big proof system, for result *)
  axiom Pz_ll (G <: GOracle.ARO):
    islossless G.o => 
    islossless Pz(G).prove.
  axiom Vz_ll (G <: GOracle.ARO):
    islossless G.o => 
    islossless Vz(G).verify.

  (* -> simulator for big proof system *)
  axiom Si_ll: islossless S.init.
  axiom So_ll: islossless S.o.
  axiom Sp_ll: islossless S.prove.

  (* -> bpriv adversary calls *)
  axiom Aa1_ll (O <: BPRIV_Oracles{A}):
    islossless O.vote =>
    islossless O.cast =>
    islossless O.board =>
    islossless O.h => 
    islossless O.g => 
    islossless A(O).a1.
  axiom Aa2_ll (O <: BPRIV_Oracles{A}):
    islossless O.board =>
    islossless O.h => 
    islossless O.g => 
    islossless A(O).a2. 

  (* -> validInd *)
  axiom C_ll (H <: HOracle.ARO):
    islossless H.o => 
    islossless C(H).validInd.

  (* -> any voting scheme *)
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

  (* -> small proof system, for ciphertexts *)
  axiom Pe_ll (H <: HOracle.ARO):
    islossless H.o => 
    islossless Pe(H).prove.
  axiom Ve_ll (H <: HOracle.ARO):
    islossless H.o => 
    islossless Ve(H).verify.
(* ** end *)


(* lemmas for lossless of encryption *)
local lemma Ek_ll (H <: HOracle.ARO):
  islossless H.o => 
  islossless IPKE(Pe, Ve, H).kgen.
proof. 
  by move => Ho; proc; auto; smt. 
qed.

local lemma Ee_ll (H <: HOracle.ARO):
  islossless H.o => 
  islossless IPKE(Pe, Ve, H).enc.
proof.
  move => Ho; proc.
  call (Pe_ll H Ho).
  by auto; progress; smt.
qed.
    
local lemma Ed_ll (H <: HOracle.ARO):
  islossless H.o => 
  islossless IPKE(Pe, Ve, H).dec.
proof.
  move => Ho; proc.    
  by wp; call (Ve_ll H Ho); wp.
qed.

(* axioms that should be proven based on LPKE *)
local lemma Ekgen_extractPk (Pe <: PSpke.Prover) (Ve <: PSpke.Verifier) 
                      (H<: HOracle.ARO):
  equiv [IPKE(Pe, Ve, H).kgen ~ IPKE(Pe, Ve, H).kgen: 
          ={glob H, glob IPKE(Pe, Ve)} ==> 
          ={glob H, glob IPKE(Pe, Ve),  res} /\ 
          res{1}.`1 = extractPk res{1}.`2  /\
          res{1}.`1 = extractPk res{1}.`2 ].
proof. 
  by proc; auto.  
qed.
 
local lemma Edec_Odec (ge: (glob IPKE(Pe, Ve)))  
                (sk2: skey)(l2: label) (c2: cipher):
  phoare [IPKE(Pe, Ve, HRO.RO).dec:  (glob IPKE(Pe, Ve)) =ge /\ 
           arg = (sk2, l2, c2) 
           ==>   
           (glob IPKE(Pe, Ve)) =ge /\
           res = dec_cipher sk2 l2 c2 HRO.RO.m ] = 1%r.
proof.
  proc; auto.
  exists * (glob Ve), c, sk, lbl ; elim* => gv cc skk lbll.
  call (Verify_to_verify gv (to_statement (extractPk skk) lbll cc.`1) cc.`2).
  by auto; progress; smt. 
qed.

local lemma Ee_eq (ge: (glob IPKE(Pe, Ve))):
  phoare [IPKE(Pe, Ve, HRO.RO).enc: 
          (glob IPKE(Pe, Ve)) = ge 
           ==> (glob IPKE(Pe, Ve)) = ge ] = 1%r.
proof.
  proc. 
  exists* (glob Pe); elim*=> gp.
  call (LPKE_prover_keepstate gp HRO.RO). 
  by auto; progress; smt.
qed.    

local lemma Eenc_dec (sk2: skey) (pk2: pkey)(l2: label) (p2: plain): 
  (pk2 = extractPk sk2) =>
  equiv [ IPKE(Pe, Ve, HRO.RO).enc ~ IPKE(Pe, Ve,HRO.RO).enc : 
          ={glob HRO.RO, glob IPKE(Pe, Ve), arg} /\ arg{1}=( pk2, l2, p2)   
          ==> 
          ={glob HRO.RO, glob IPKE(Pe, Ve),  res} /\ 
          Some p2 = dec_cipher sk2 l2 res{1} HRO.RO.m{1} ].
proof.
  move => kp.
  proc.
  seq 2 2: (={HRO.RO.m, glob Pe, glob Ve, pk, lbl, p, c, r} /\
            (pk{1}, lbl{1}, p{1}) = (pk2, l2, p2)/\
            c{1} = encrypt pk{1} p{1} r{1}).
    by auto.
  exists* pk{1}, lbl{1}, c{1}, p{1}, r{1};
  elim*=> pkk lbll cc pp rr.
  call (Prover_to_verify (to_statement pkk lbll cc) (to_witness pp rr)).  
  by auto; progress; smt. 
qed.
   
local lemma Eenc_decL (ge: (glob IPKE(Pe, Ve))) (sk2: skey) 
                 (pk2: pkey)(l2: label) (p2: plain): 
  (pk2 = extractPk sk2) =>
  phoare [ IPKE(Pe, Ve, HRO.RO).enc : 
           (glob IPKE(Pe, Ve)) = ge /\ arg=( pk2, l2, p2)
          ==> 
          (glob IPKE(Pe, Ve)) = ge /\ 
          Some p2 = dec_cipher sk2 l2 res HRO.RO.m ]= 1%r.         
proof.
  move => kp.
  proc.
  seq 2: (((glob Pe), (glob Ve)) = ge /\ 
          (pk, lbl, p) = (pk2, l2, p2) /\
          c = encrypt pk p r)=>//=.
    by auto; progress; smt.
  
    exists* (glob Pe), pk, lbl, c, p, r;
    elim*=> gp pkk lbll cc pp rr.
    call{1} (Prover_to_verify_left gp (to_statement pkk lbll cc) (to_witness pp rr)).
    by auto; progress; smt.

  by hoare; auto; progress; smt.
qed. 

(* Lemma bounding BPRIV *)
lemma bpriv &m: 
   `|Pr[BPRIV_L(MV(IPKE(Pe, Ve), Pz, Vz, C), A, HRO.RO, G).main() @ &m : res] -
     Pr[BPRIV_R(MV(IPKE(Pe, Ve), Pz, Vz, C), A, HRO.RO, G, S).main() @ &m :res]| 
<=
     Pr[VFR(IPKE(Pe, Ve), BVFR(MV(IPKE(Pe, Ve), Pz, Vz, C), A), 
            Rz(IPKE(Pe,Ve)), HRO.RO, G).main() @ &m : res] +
     Pr[VFR(IPKE(Pe, Ve), BVFR(MV(IPKE(Pe, Ve), Pz, Vz, C), A), 
            Rz(IPKE(Pe,Ve)), HRO.RO, S).main() @ &m : res] +
   `|Pr[ZK_L(Rz(IPKE(Pe,Ve),HRO.RO), Pz, 
             BZK(IPKE(Pe, Ve), Pz, C, Vz, A, HRO.RO), G).main() @ &m : res] -
     Pr[ZK_R(Rz(IPKE(Pe,Ve),HRO.RO), S, 
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
  by rewrite (bpriv G (IPKE(Pe,Ve)) S Vz Pz Rz C A Gi_ll Go_ll Aa1_ll Aa2_ll Pz_ll 
                    Vz_ll Ek_ll Ee_ll Ed_ll Si_ll So_ll Sp_ll C_ll Vval_ll Vvot_ll 
                    relConstraint Rho_weight (Ekgen_extractPk Pe Ve) Edec_Odec 
                    Ee_eq Eenc_decL Eenc_dec &m).   
qed.
end section BPRIV.

(* Strong Consistency PROPERTY *)
(* --------------------------------------------------------------------------*)
section Consistency.

declare module H : HOracle.Oracle { BP}.
declare module G : GOracle.Oracle { BP, HRO.RO, H}.
declare module S : Simulator      { HRO.RO, H, G}.
declare module Vz: Verifier       { HRO.RO, H, G, S}.
declare module Pz: Prover         { HRO.RO, H, G, S, Vz}.
declare module Ve: PSpke.Verifier { BP, H, G, S, Vz, Pz}.
declare module Pe: PSpke.Prover   { BP, H, G, S, Vz, Pz, Ve}.
declare module C : ValidInd       { BP, H, HRO.RO, G, S, Vz, Pz, Ve, Pe}.

declare module AC2: SConsis2_Adv {BP, H, HRO.RO, G}.
declare module AC3: SConsis3_Adv {BP, H, Pe, Ve, C, G}.

(* ** ASSUMPTIONS ** *)
(* ** start *)
  (* lossless *)
  axiom Gi_ll: islossless G.init.
  axiom Go_ll: islossless G.o.

  axiom C_ll (H<: HOracle.ARO):
    islossless H.o =>
    islossless C(H).validInd.

  axiom Pz_ll (G <: GOracle.ARO): 
    islossless G.o =>
    islossless Pz(G).prove. 

  axiom AC2_ll (O <: SCons_Oracle { AC2 }):
    islossless O.h       =>
    islossless O.g       =>
    islossless AC2(O).main. 

  (* axiom for result distribution *)
  axiom Rho_weight (x: (ident * plain option) list):
    weight (Rho x)= 1%r.

  (* axiom for transforming C.validInd to validInd operator *)
  axiom validInd_ax (gc: (glob C)) (pk: pkey) (b: ident * label * cipher):
    phoare[C(HRO.RO).validInd: 
            (glob C) = gc /\ arg = (b, pk) 
            ==>
            (glob C) = gc /\ res = validInd pk b HRO.RO.m] = 1%r.
(* ** end *)

(* axioms that should be proven based on LPKE *)
local lemma Ek_ll (H <: HOracle.ARO): 
  islossless H.o =>
  islossless IPKE(Pe, Ve, H).kgen.
proof.
  by move => Ho; proc; auto; smt.
qed.

(* Lemma bounding strong consistency part 1*)
lemma consis1(id: ident, v: plain, l: label) &m: 
   Pr[SConsis1(MV(IPKE(Pe,Ve),Pz,Vz,C), CE(IPKE(Pe,Ve)), H, G).main(id,v, l) @ &m: res]  
   >=
   Pr[PKEvf.Correctness(IPKE(Pe,Ve), H).main(v,l) @ &m: res].
proof.
  by rewrite (consis1 H G (IPKE(Pe, Ve)) S Vz Pz C AC2 AC3 Gi_ll Go_ll 
                C_ll Pz_ll Ek_ll AC2_ll Rho_weight validInd_ax id v l &m). 
qed.  

(* Lemma bounding strong consistency part 2*)
lemma consis2 &m:
  Pr[SConsis2(MV(IPKE(Pe,Ve), Pz, Vz, C), C, AC2, HRO.RO, G).main() @ &m: res] = 1%r.
proof. 
  by rewrite (consis2 H G (IPKE(Pe, Ve)) S Vz Pz C AC2 AC3 Gi_ll Go_ll 
                 C_ll Pz_ll Ek_ll AC2_ll Rho_weight validInd_ax&m).
qed.

(* Lemma bounding strong consistency part 3*)
equiv consis3 &m:
    SConsis3_L(MV(IPKE(Pe,Ve), Pz, Vz, C), C, AC3, H, G).main ~ 
    SConsis3_R(MV(IPKE(Pe,Ve), Pz, Vz, C), CE(IPKE(Pe,Ve)), C, AC3, H, G).main
    : ={glob H, glob G, glob IPKE(Pe,Ve), glob C, glob AC3} ==> ={res}.
proof.
  by rewrite (consis3 H G (IPKE(Pe, Ve)) S Vz Pz C AC2 AC3 Gi_ll Go_ll 
                C_ll Pz_ll Ek_ll AC2_ll Rho_weight validInd_ax &m). 
qed.

end section Consistency.

(* Strong Correctness PROPERTY *)
(* --------------------------------------------------------------------------*)
section Correctness.

declare module Pe: PSpke.Prover    { BS, BP, BSC, BSCorr, HRO.RO}.
declare module Ve: PSpke.Verifier  { BS, BP, BSC, BSCorr, HRO.RO, Pe}.
declare module C : ValidInd        { BS, BP, BSC, BSCorr, HRO.RO, Pe, Ve}.
declare module S : Simulator       { BSC, BSCorr, BP, BS, HRO.RO, Pe, Ve, C}.
declare module Vz: Verifier        { BS, BP, BSCorr, HRO.RO, Pe, Ve, C, S}.
declare module Pz: Prover          { BS, BP, BSCorr, HRO.RO, Pe, Ve, C, S, Vz}.
declare module A : BPRIV_Adv       { BSC, BS, BSCorr, BP, S, Pe, Ve, C, Vz, Pz, HRO.RO}.

(* ** ASSUMPTIONS ** *)
(* ** start *)
  (* lossless *)
  axiom Pe_ll (H<: HOracle.ARO):
    islossless H.o=>
    islossless Pe(H).prove.

  axiom Ve_ll (H<: HOracle.ARO):
    islossless H.o=>
    islossless Ve(H).verify.

  axiom AC_ll (AS <: SCorr_Adv') 
              (V<: VotingScheme{AS}) (O <: SCorr_Oracle {AS}):
    islossless O.h => 
    islossless O.g => 
    islossless O.test =>
    islossless AS(V,O).main.

  axiom So_ll: islossless S.o.
  axiom Si_ll: islossless S.init.

  (* at least 2 distinct votes *)
  axiom v_distinct: v_def_0 <> v_def_1.

  (* axiom linking proof to verification (two-sided) *)
  axiom Prover_to_verify (s: h_stm) (w: h_wit):
    equiv[Pe(HRO.RO).prove ~ Pe(HRO.RO).prove: 
         ={glob HRO.RO, glob Pe, arg} /\ arg{1} = (s, w)
         ==>
         ={glob HRO.RO, glob Pe, res} /\
         verify s res{1} HRO.RO.m{1}].

  (* axiom linking proof to verification (one-sided) *)
  axiom Prover_to_verify_left (gp: (glob Pe)) (s: h_stm) (w: h_wit):
    phoare[Pe(HRO.RO).prove: 
          (glob Pe) = gp /\ arg = (s, w)
         ==>
         (glob Pe) = gp /\ verify s res HRO.RO.m]= 1%r.

  (* axiom transforming Ve.verify in verify opertor *)
  axiom Verify_to_verify (gv: (glob Ve)) (s: h_stm) (p: h_prf):
    phoare[Ve(HRO.RO).verify: 
          (glob Ve) = gv /\ arg = (s, p)
         ==>
          (glob Ve) = gv /\
         res = verify s p HRO.RO.m] = 1%r.

  (* encryption always implies validInd true *)
  axiom enc_to_validInd (pkx: pkey) (id: ident) (v: plain) (l : label):
    equiv[IPKE(Pe,Ve,HRO.RO).enc ~ IPKE(Pe,Ve,HRO.RO).enc: 
         ={glob HRO.RO, glob IPKE(Pe,Ve), arg} /\ arg{1} = (pkx,l,v) 
         ==> 
         ={res, glob IPKE(Pe,Ve), glob HRO.RO} /\
          validInd pkx (id, l, res{1}) HRO.RO.m{1}].

  (* axiom linking C.validInd to validInd operator *)
  axiom validInd_ax (gc: (glob C)) (pk: pkey) (b: ident * label * cipher):
    phoare[C(HRO.RO).validInd: 
            (glob C) = gc /\ arg = (b, pk) 
            ==>
            (glob C) = gc /\ res = validInd pk b HRO.RO.m] = 1%r.

(* ** end *)

(* axioms that should be proven based on LPKE *)
local lemma Eenc_decL (ge: (glob IPKE(Pe,Ve))) (sk2: skey) 
                 (pk2: pkey)(l2: label) (p2: plain): 
  (pk2 = extractPk sk2) =>
  phoare [IPKE(Pe,Ve,HRO.RO).enc : (glob IPKE(Pe,Ve)) = ge /\ arg=( pk2, l2, p2)
          ==> 
          (glob IPKE(Pe,Ve)) = ge /\ 
          Some p2 = dec_cipher sk2 l2 res HRO.RO.m ]= 1%r.
proof.
  move => kp.
  proc.
  seq 2: ( (glob IPKE(Pe, Ve)) = ge /\ 
          (pk, lbl, p) = (pk2, l2, p2) /\
          c = encrypt pk p r)=>//=.
    by auto; progress; smt.  
    exists* (glob Pe), pk, lbl, c, p, r;
    elim*=> gp pkk lbll cc pp rr.
    call{1} (Prover_to_verify_left gp (to_statement pkk lbll cc) (to_witness pp rr)).
    by auto; progress; smt.

  by hoare; auto; progress; smt.
qed.
  
local lemma Eenc_dec (sk2: skey) (pk2: pkey)(l2: label) (p2: plain): 
  (pk2 = extractPk sk2) =>
  equiv [IPKE(Pe, Ve, HRO.RO).enc ~ IPKE(Pe, Ve,HRO.RO).enc : 
          ={glob HRO.RO, glob IPKE(Pe, Ve), arg} /\ arg{1}=( pk2, l2, p2)   
          ==> 
          ={glob HRO.RO, glob IPKE(Pe, Ve),  res} /\ 
          Some p2 = dec_cipher sk2 l2 res{1} HRO.RO.m{1} ].
proof.
  move => kp.
  proc.
  seq 2 2: (={HRO.RO.m, glob Pe, glob Ve, pk, lbl, p, c, r} /\
            (pk{1}, lbl{1}, p{1}) = (pk2, l2, p2)/\
            c{1} = encrypt pk{1} p{1} r{1}).
    by auto.
  exists* pk{1}, lbl{1}, c{1}, p{1}, r{1};
  elim*=> pkk lbll cc pp rr.
  call (Prover_to_verify (to_statement pkk lbll cc) (to_witness pp rr)).  
  by auto; progress; smt. 
qed.

local lemma Edec_Odec (ge: (glob IPKE(Pe, Ve)))  
                (sk2: skey)(l2: label) (c2: cipher):
  phoare [IPKE(Pe, Ve, HRO.RO).dec:  (glob IPKE(Pe, Ve)) =ge /\ 
           arg = (sk2, l2, c2) 
           ==>   
           (glob IPKE(Pe, Ve)) =ge /\
           res = dec_cipher sk2 l2 c2 HRO.RO.m ] = 1%r.
proof.
  proc; auto.
  exists * (glob Ve), c, sk, lbl ; elim* => gv cc skk lbll.
  call (Verify_to_verify gv (to_statement (extractPk skk) lbll cc.`1) cc.`2).
  by auto; progress; smt. 
qed.

local lemma Ekgen_extractPk (H<: HOracle.ARO):
  equiv [IPKE(Pe, Ve, H).kgen ~ IPKE(Pe, Ve, H).kgen: 
          ={glob H, glob IPKE(Pe, Ve)} 
          ==> 
          ={glob H, glob IPKE(Pe, Ve),  res} /\ 
          res{1}.`1 = extractPk res{1}.`2  /\
          res{1}.`1 = extractPk res{1}.`2 ].
proof.
  by proc; auto. 
qed.

local lemma Ekgen_extractPkL (H<: HOracle.ARO):
  phoare [IPKE(Pe, Ve, H).kgen: true 
           ==>   
           res.`1 = extractPk res.`2 ] = 1%r.
proof.
  by proc; auto; progress; smt.
qed.

(* lossless axioms that should be proven based on LPKE *) 
local lemma Ek_ll(H <: HOracle.ARO): 
  islossless H.o =>
  islossless IPKE(Pe, Ve, H).kgen.
proof.
  move => Ho; proc.
  by auto ; progress; smt.
qed.

local lemma Ee_ll(H <: HOracle.ARO): 
  islossless H.o =>
  islossless IPKE(Pe, Ve, H).enc.
proof.
  move =>Ho; proc.
  call (Pe_ll H Ho).
  by auto; progress; smt.
qed.
 
local lemma Ed_ll(H <: HOracle.ARO): 
  islossless H.o =>
  islossless IPKE(Pe,Ve,H).dec.
proof.
  move => Ho; proc.
  wp; call (Ve_ll H Ho).
  by auto.
qed.


(* Lemma bounding strong correctness, general version *)
lemma scorr (AS <: SCorr_Adv' { IPKE(Pe,Ve), Pz, Vz, C, HRO.RO, BSC, BS}) 
            (G  <: GOracle.Oracle { BS, BP, BSC, BSCorr, HRO.RO, IPKE(Pe,Ve), Pz, Vz, C, AS}) &m:
islossless G.init =>
islossless G.o =>
  Pr[SCorr(MV(IPKE(Pe,Ve), Pz, Vz, C), 
           AS(MV(IPKE(Pe,Ve),Pz,Vz,C)), HRO.RO, G).main() @ &m: BSC.valid ] = 
`|Pr[Ind1CCA(IPKE(Pe,Ve), 
             INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, C), 
                       AS(MV(IPKE(Pe,Ve), Pz, Vz, C)), G, HRO.RO)), 
             HRO.RO,Left).main()  @ &m: res /\  size BS.encL <= 1] -
  Pr[Ind1CCA(IPKE(Pe,Ve), 
             INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, C), 
                       AS(MV(IPKE(Pe,Ve), Pz, Vz, C)), G, HRO.RO)),
             HRO.RO,Right).main()  @ &m: res /\  size BS.encL <= 1]|.
proof. 
 by exact (scorr (IPKE(Pe,Ve)) S Vz Pz C A v_distinct enc_to_validInd validInd_ax 
                 Eenc_decL Eenc_dec Edec_Odec Ekgen_extractPk Ekgen_extractPkL
                 Ek_ll Ee_ll Ed_ll So_ll Si_ll AC_ll AS G &m).
qed.

(* Lemma bounding strong correctness, bpriv case *)
lemma scorr_bpriv (LR<: LorR { BS, BP, BIND, BIND2, BSCorr, BSC, 
            HRO.RO, A, Ve, C, Vz, Pz, Pe, S}) &m:
  Pr[SCorr (MV(IPKE(Pe,Ve),Pz,Vz, C), 
            BSCorr(MV(IPKE(Pe,Ve),Pz,Vz, C),A, LR), HRO.RO, S).main() @ &m: BSC.valid] = 
`|Pr[Ind1CCA(IPKE(Pe,Ve),
             INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, C), 
                       BSCorr(MV(IPKE(Pe,Ve),Pz,Vz, C),A, LR), S, HRO.RO)),
             HRO.RO,Left).main() @ &m: res /\  size BS.encL <= 1] -
  Pr[Ind1CCA(IPKE(Pe,Ve),
             INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, C),
                       BSCorr(MV(IPKE(Pe,Ve),Pz,Vz, C),A, LR), S, HRO.RO)),
             HRO.RO,Right).main() @ &m: res /\  size BS.encL <= 1]|. 
proof. 
  by rewrite (scorr_bpriv (IPKE(Pe,Ve)) S Vz Pz C A v_distinct enc_to_validInd validInd_ax 
                 Eenc_decL Eenc_dec Edec_Odec Ekgen_extractPk Ekgen_extractPkL
                 Ek_ll Ee_ll Ed_ll So_ll Si_ll AC_ll LR &m). 
qed.

end section Correctness.

section Weeding_ALL.

declare module C: ValidInd        {BS, BP, BSCorr, HRO.RO, BSC}. 
declare module Pz: Prover         {C, BS, BP, BSCorr, HRO.RO}.
declare module Vz: Verifier       {C, Pz, BS, BP, BSCorr, HRO.RO}.
declare module G : GOracle.Oracle {C, Pz, Vz, BP}.
declare module H : HOracle.Oracle {C, Pz, Vz, G, BP}.
declare module S : Simulator      {C, Pz, Vz, G, H, BP, BSC, BSCorr, BS, HRO.RO}.
declare module A : BPRIV_Adv      {C, Pz, Vz, G, H, S, BSC, BS, BSCorr, BP, HRO.RO}.

(* this are needed for the LPKE scheme *)
declare module Ve: PSpke.Verifier
                  { H, BP, BS, BPS, BSC, BSCorr, BIND, HRO.RO, G, S, Vz, Pz, C, A,
                    PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv, BPRIV_SB, BIND2}.
declare module Pe: PSpke.Prover
                  { H, BP, BS, BPS, BSC, BSCorr, BIND, HRO.RO, G, S, Vz, Pz, C, A, Ve,
                    PKEvf.H.Count, PKEvf.H.HybOrcl, WrapAdv, BPRIV_SB, BIND2}.

(* ** ASSUMPTIONS ** *)
(* ** start *)
  (* injectivity over label *)
  axiom F_inj(x y: ident): 
    Flabel x = Flabel y => x = y.
  
  (* at least two distinct plaintexts *)
  axiom v_distinct: v_def_0 <> v_def_1.

  (* encryption always implies validInd true *)
  axiom enc_to_validInd (pkx: pkey) (id: ident) (v: plain) (l : label):
    equiv[IPKE(Pe,Ve,HRO.RO).enc ~ IPKE(Pe,Ve,HRO.RO).enc: 
         ={glob HRO.RO, glob IPKE(Pe,Ve), arg} /\ arg{1} = (pkx,l,v) 
         ==> 
         ={res, glob IPKE(Pe,Ve), glob HRO.RO} /\
          validInd pkx (id, l, res{1}) HRO.RO.m{1}].

  (* axiom linking C.validInd to validInd operator *)
  axiom validInd_ax (gc: (glob C)) (pk: pkey) (b: ident * label * cipher):
    phoare[ C(HRO.RO).validInd: 
            (glob C) = gc /\ arg = (b, pk) 
            ==>
            (glob C) = gc /\ res = validInd pk b HRO.RO.m] = 1%r.

  (* axiom transforming proof to verification (one-sided) *)
  axiom Prover_to_verify_left (gp: (glob Pe)) (s: h_stm) (w: h_wit):
    phoare[Pe(HRO.RO).prove: 
          (glob Pe) = gp /\ arg = (s, w)
          ==>
          (glob Pe) = gp /\ verify s res HRO.RO.m]= 1%r.

  (* axiom transforming proof to verification (two-sided) *)
  axiom Prover_to_verify (s: h_stm) (w: h_wit):
    equiv[Pe(HRO.RO).prove ~ Pe(HRO.RO).prove: 
         ={glob HRO.RO, glob Pe, arg} /\ arg{1} = (s, w)
         ==>
         ={glob HRO.RO, glob Pe, res} /\
         verify s res{1} HRO.RO.m{1}].

  (* axiom linking C.verify to verify operator *)
  axiom Verify_to_verify (gv: (glob Ve)) (s: h_stm) (p: h_prf):
    phoare[Ve(HRO.RO).verify: (glob Ve) = gv /\ arg = (s, p)
         ==>
         (glob Ve) = gv /\
         res = verify s p HRO.RO.m] = 1%r.

  (* lossless *)
  axiom Pe_ll (H<: HOracle.ARO):
    islossless H.o=>
    islossless Pe(H).prove.

  axiom Ve_ll (H<: HOracle.ARO):
    islossless H.o=>
    islossless Ve(H).verify.

  axiom So_ll: islossless S.o.
  axiom Si_ll: islossless S.init.

  axiom AC_ll (AS <: SCorr_Adv') 
              (V<: VotingScheme{AS}) (O <: SCorr_Oracle {AS}):
    islossless O.h => 
    islossless O.g => 
    islossless O.test =>
    islossless AS(V,O).main.

(* ** end *)

(* axioms that should be proven based on LPKE *)
local lemma Eenc_decL (ge: (glob IPKE(Pe, Ve))) (sk2: skey) 
                 (pk2: pkey)(l2: label) (p2: plain): 
  (pk2 = extractPk sk2) =>
  phoare [ IPKE(Pe, Ve, HRO.RO).enc : 
           (glob IPKE(Pe, Ve)) = ge /\ arg=( pk2, l2, p2)
          ==> 
          (glob IPKE(Pe, Ve)) = ge /\ 
          Some p2 = dec_cipher sk2 l2 res HRO.RO.m ]= 1%r.         
proof.
  move => kp.
  proc.
  seq 2: (((glob Pe), (glob Ve)) = ge /\ 
          (pk, lbl, p) = (pk2, l2, p2) /\
          c = encrypt pk p r)=>//=.
    by auto; progress; smt.  
    exists* (glob Pe), pk, lbl, c, p, r;
    elim*=> gp pkk lbll cc pp rr.
    call{1} (Prover_to_verify_left gp (to_statement pkk lbll cc) (to_witness pp rr)).

    by auto; progress; smt.

  by hoare; auto; progress; smt.
qed.

local lemma Eenc_dec (sk2: skey) (pk2: pkey)(l2: label) (p2: plain): 
  (pk2 = extractPk sk2) =>
  equiv [ IPKE(Pe, Ve, HRO.RO).enc ~ IPKE(Pe, Ve, HRO.RO).enc : 
          ={glob HRO.RO, glob IPKE(Pe, Ve), arg} /\ arg{1}=( pk2, l2, p2)   
          ==> 
          ={glob HRO.RO, glob IPKE(Pe, Ve),  res} /\ 
          Some p2 = dec_cipher sk2 l2 res{1} HRO.RO.m{1} ].
proof.
  move => kp.
  proc.
  seq 2 2: (={HRO.RO.m, glob Pe, glob Ve, pk, lbl, p, c, r} /\
            (pk{1}, lbl{1}, p{1}) = (pk2, l2, p2)/\
            c{1} = encrypt pk{1} p{1} r{1}).
    by auto.
  exists* pk{1}, lbl{1}, c{1}, p{1}, r{1};
  elim*=> pkk lbll cc pp rr.
  call (Prover_to_verify (to_statement pkk lbll cc) (to_witness pp rr)).  
  by auto; progress; smt. 
qed.

local lemma Edec_Odec (ge: (glob IPKE(Pe, Ve)))  
                (sk2: skey)(l2: label) (c2: cipher):
  phoare [ IPKE(Pe, Ve, HRO.RO).dec:  (glob IPKE(Pe, Ve)) =ge /\ 
           arg = (sk2, l2, c2) 
           ==>   
           (glob IPKE(Pe, Ve)) =ge /\
           res = dec_cipher sk2 l2 c2 HRO.RO.m ] = 1%r.
proof.
  proc; auto.
  exists * (glob Ve), c, sk, lbl ; elim* => gv cc skk lbll.
  call (Verify_to_verify gv (to_statement (extractPk skk) lbll cc.`1) cc.`2).
  by auto; progress; smt. 
qed.

(* equivalence show that MV.valid and MV'.valid are the same, 
   if the label is injective *)
equiv same_valid (Gx<: GOracle.ARO {H, C})
                       (bbx: (ident * label * cipher) list)
                       (uLx: (ident, label) map) 
                       (bx: ident * label * cipher) 
                       (pkx: pkey):
  MV(IPKE(Pe,Ve), Pz, Vz, C, H, Gx).valid ~ MV'(IPKE(Pe,Ve), Pz, Vz, C, H, Gx).valid
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
  by rewrite (same_valid C (IPKE(Pe,Ve)) Pz Vz G H S A F_inj Gx bbx uLx bx pkx).
qed.

(* Lemma bounding strong correctness for MiniVoting' *)
lemma scorr_bound_mv' (AS <: SCorr_Adv' { IPKE(Pe,Ve), Pz, Vz, C, HRO.RO, BSC, BS}) 
                      (G  <: GOracle.Oracle { BS, BP, BSC, BSCorr, HRO.RO, 
                                              IPKE(Pe,Ve), Pz, Vz, C, AS, S, A}) &m:
  islossless G.init =>
  islossless G.o =>
  Pr[SCorr(MV'(IPKE(Pe,Ve), Pz, Vz, C), 
           AS(MV'(IPKE(Pe,Ve),Pz,Vz,C)), HRO.RO, G).main() @ &m: BSC.valid ] <= 
`|Pr[Ind1CCA(IPKE(Pe,Ve),
             INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, C), 
             AS(MV(IPKE(Pe,Ve), Pz, Vz, C)), G, HRO.RO)),
             HRO.RO,Left).main()  @ &m: res /\  size BS.encL <= 1] -
  Pr[Ind1CCA(IPKE(Pe,Ve),
             INDB(Bmem(MV(IPKE(Pe,Ve), Pz, Vz, C), 
             AS(MV(IPKE(Pe,Ve), Pz, Vz, C)), G, HRO.RO)),
             HRO.RO,Right).main()  @ &m: res /\  size BS.encL <= 1]|.
proof.  
  cut T:= scorr_mv' C (IPKE(Pe,Ve)) Pz Vz G HRO.RO S A v_distinct enc_to_validInd 
          validInd_ax Eenc_decL Eenc_dec Edec_Odec _ _ _ _ _ So_ll Si_ll AC_ll AS G &m.
   + move => Hh; by proc; auto.
   + move => Hh; by proc; auto; progress; smt.
   + move => Hh Ho; by proc; auto; progress; smt.
   + move => Hh Ho; by proc; call (Pe_ll Hh Ho); auto; progress; smt. 
   + move => Hh Ho; by proc; wp; call (Ve_ll Hh Ho); auto; progress; smt. 
  by apply T.
qed.

end section Weeding_ALL.

(* Voting Friendly Relation *)
(* --------------------------------------------------------------------------*)
section VotingFriendlyRelation.

declare module G : GOracle.Oracle { BS, BP, HRO.RO}.
declare module S : Simulator      { BS, BP, HRO.RO, G}.
declare module Vz: Verifier       { BP, HRO.RO, G, S}.
declare module Pz: Prover         { BP, HRO.RO, G, S, Vz}.
declare module C : ValidInd       { BS, BP, HRO.RO, G, S, Vz, Pz}.
declare module A : BPRIV_Adv      { BS, BP, HRO.RO, G, S, Vz, Pz, C}.

(* this are needed for the LPKE scheme *)
declare module Ve: PSpke.Verifier { BS, BP, HRO.RO, G, S, Vz, Pz, C, A}.
declare module Pe: PSpke.Prover   { BS, BP, HRO.RO, G, S, Vz, Pz, C, A, Ve}.

(* ** ASSUMPTIONS ** *)
(* ** start *)
  (* lossless *)
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

  axiom Pe_ll (H<: HOracle.ARO):
    islossless H.o=>
    islossless Pe(H).prove.

  axiom Ve_ll (H<: HOracle.ARO):
    islossless H.o=>
    islossless Ve(H).verify.

  (* axiom transforming Ve.verify in verify operator *)
  axiom Verify_to_verify (gv: (glob Ve)) (s: h_stm) (p: h_prf):
    phoare[Ve(HRO.RO).verify: 
          (glob Ve) = gv /\ arg = (s, p)
         ==>
          (glob Ve) = gv /\
         res = verify s p HRO.RO.m] = 1%r.

  (* axiom for result distribution *)
  axiom Rho_weight (x: (ident * plain option) list) :
    weight (Rho x)= 1%r.

(* axioms that should be proven based on LPKE *)
local lemma Ed_ll (H<:HOracle.ARO):
  islossless H.o=>
  islossless IPKE(Pe,Ve,H).dec.
proof.
  move => Ho; proc.
  by wp; call (Ve_ll H Ho); wp.
qed.

local lemma Ee_ll (H<:HOracle.ARO):
  islossless H.o=>
  islossless IPKE(Pe,Ve,H).enc.
proof.
  move => Ho; proc.
  call (Pe_ll H Ho).
  by auto; progress; smt. 
qed.

local lemma Ekgen_extractPk (H<: HOracle.ARO):
  phoare [IPKE(Pe,Ve,H).kgen : true ==> 
          res.`1 = extractPk res.`2 ] = 1%r.
proof.
  by proc; auto; progress; smt.
qed.

local lemma Edec_Odec (ge: (glob IPKE(Pe,Ve))) (sk2: skey)(l2: label) (c2: cipher):
  phoare [IPKE(Pe,Ve,HRO.RO).dec:  
           (glob IPKE(Pe,Ve)) =ge /\ arg = (sk2, l2, c2) 
           ==>   
           (glob IPKE(Pe,Ve)) =ge /\
           res = dec_cipher sk2 l2 c2 HRO.RO.m ] = 1%r.
proof.
  proc; auto.
  exists * (glob Ve), c, sk, lbl ; elim* => gv cc skk lbll.
  call (Verify_to_verify gv (to_statement (extractPk skk) lbll cc.`1) cc.`2).
  by auto; progress; smt. 
qed.
   
(* lemma bounding vfr for DecRelation *)
lemma bound_vfr (Gx<: GOracle.Oracle {A, BP, BS, HRO.RO}) &m:
  islossless Gx.init =>
  islossless Gx.o =>
  Pr[VFR(IPKE(Pe,Ve), BVFR(MV(IPKE(Pe,Ve), Pz, Vz, C), A), 
         DecRelation(IPKE(Pe,Ve)), HRO.RO, Gx).main () @ &m : res] = 0%r.
proof.
  by exact (bound_vfr G S Vz Pz C A (IPKE(Pe,Ve)) Aa1_ll So_ll Si_ll Go_ll 
              Gi_ll Co_ll Ed_ll Ee_ll Rho_weight Ekgen_extractPk Edec_Odec Gx &m).  
qed.
 
(* lemma bounding vfr for DecRelation (left) *)
lemma bound_vfr_left &m:
  Pr[VFR(IPKE(Pe,Ve), BVFR(MV(IPKE(Pe,Ve), Pz, Vz, C), A), 
         DecRelation(IPKE(Pe,Ve)), HRO.RO, G).main () @ &m : res] = 0%r.
proof.
  by rewrite (bound_vfr_left G S Vz Pz C A (IPKE(Pe,Ve)) Aa1_ll So_ll Si_ll Go_ll 
                Gi_ll Co_ll Ed_ll Ee_ll Rho_weight Ekgen_extractPk Edec_Odec &m). 
qed.

(* lemma bounding vfr for DecRelation (right) *)
lemma bound_vfr_right &m:
  Pr[VFR(IPKE(Pe,Ve), BVFR(MV(IPKE(Pe,Ve), Pz, Vz, C), A), 
         DecRelation(IPKE(Pe,Ve)), HRO.RO, S).main () @ &m : res] = 0%r.
proof.
  by rewrite (bound_vfr_right G S Vz Pz C A (IPKE(Pe,Ve)) Aa1_ll So_ll Si_ll Go_ll 
                Gi_ll Co_ll Ed_ll Ee_ll Rho_weight Ekgen_extractPk Edec_Odec &m). 
qed.

(* lemma bounding vfr for NoRelation *)
lemma bound2_vfr (Gx<: GOracle.Oracle {A, BP, BS, HRO.RO}) &m:
  islossless Gx.init =>
  islossless Gx.o => 
  Pr[VFR(IPKE(Pe,Ve), BVFR(MV(IPKE(Pe,Ve), Pz, Vz, C), A), 
        NoRelation(IPKE(Pe,Ve)), HRO.RO, Gx).main () @ &m : res] = 0%r.
proof.
 by exact (bound2_vfr G S Vz Pz C A (IPKE(Pe,Ve)) Aa1_ll  So_ll Si_ll Go_ll 
             Gi_ll Co_ll Ed_ll Ee_ll Rho_weight Ekgen_extractPk Edec_Odec Gx &m). 
qed.


end section VotingFriendlyRelation.