require import Int Bool Real FMap.
require import Distr Option List Pair.
require import LeftOrRight.
require (*  *) VotingSecurity.
require (*  *) VFR Finite.

(* ---------------------------------------------------------------------- *)
(* Preliminaries *)

(* types *)
type ident.   (* ident *)
type vote.    (* vote *)
type result.  (* result *)
type pubBB.   (* public bulletin box *)

type label.   (* label *)
type cipher.  (* chipertext *)
type pkey.    (* public key *)
type skey.    (* secret key *)

type prf.     (* proof *)

type h_in, h_out. (* input and output for encryption   random oracle H *)
type g_in, g_out. (* input and output for proof system random oracle G *)

(* distributions *)
op d_ids  : ident distr.
op dh_out : h_out distr.
op dg_out : g_out distr.
(* voting algorithms *)
op Publish: (ident * label * cipher) list -> pubBB.
op Rho    : (ident * vote option) list -> result distr.
op Flabel : ident                      -> label.

op part : { int | 0< part} as part_pos.
(* bound on honest calls by bpriv aadversary *)
op n : { int | 0 < n } as n_pos.
(* bound on the number of cast ballots that pass valid : BP.qCa < k *)
op k : { int | 0 < k} as p_pos.
(* the public key assignes to a secret key *)
op extractPk: skey -> pkey.

(* remove identity from ballots *)
op remID (xs: (ident * label * cipher) list) = 
  with xs = []  => []
  with xs = b::ys => [(b.`3,b.`2)] ++ (remID ys). 

(* axioms for distributions *)
axiom d_ids_ll       : is_lossless d_ids.
axiom is_finite_h_in : Finite.is_finite predT <:h_in>.
axiom distr_h_out    : is_lossless dh_out.

clone export VFR as VFRmv with 
  type ident    <- ident,
  type vote   <- vote,
  type result <- result,
  type label  <- label,
  type cipher <- cipher,
  type pkey   <- pkey,
  type skey   <- skey,
  type prf    <- prf,
  type pubBB  <- pubBB,
  type h_in   <- h_in,
  type h_out  <- h_out,
  type g_in   <- g_in,
  type g_out  <- g_out,
  op dh_out   <- dh_out,
  op dg_out   <- dg_out,
  op Publish  <- Publish,
  op Rho      <- Rho,
  op n        <- n
  proof *.
  realize n_pos. by apply n_pos. qed.

clone export VotingSecurity as VSmv with
  type ident  <- ident,
  type vote   <- vote,
  type result <- result,
  type pubBB  <- pubBB,
  type label  <- label,
  type ballot <- cipher,
  type pkey   <- pkey,
  type skey   <- skey,
  type prf    <- prf,
  type h_in   <- h_in,
  type h_out  <- h_out,
  type g_in   <- g_in,
  type g_out  <- g_out,
  op dh_out   <- dh_out,
  op dg_out   <- dg_out,
  op Publish  <- Publish,
  op Rho      <- Rho,
  op n        <- n,
  op k        <- k,
  op part     <- part 
  proof *.  
  realize n_pos. by apply n_pos. qed. 
  realize p_pos. by apply p_pos. qed.
  realize part_pos. by apply part_pos. qed.



(* ---------------------------------------------------------------------- *)
(* Definition *)

(* MiniVoting scheme *)
module MV (E: Scheme, P: Prover, Ve: Verifier, 
           C:ValidInd, H: HOracle.ARO, G: GOracle.ARO) = {

  (* setup algorithm *)
  proc setup(nr: int): pkey * skey * (ident, label) map = {
    var i, id, uL, pk, sk;
    
    i <- 0;
    uL <- empty;
    (pk, sk) <@ E(H).kgen();
    (* assign labels for ids *)
    while (i < nr){
      id     <$ d_ids;
      uL.[id]<- Flabel(id);
      i      <- i + 1;
    }
    
    return (pk, sk, uL);
  }
  
  (* validation algorithm *)
  proc valid (bb: (ident * label * cipher) list, 
              uL: (ident, label) map, 
              b: (ident * label * cipher),
              pk: pkey): bool = {
    var ev1, ev2, ev3;
    var b', i;

    i <- 0;
    ev1 <- false;
    ev2 <- false;
    ev3 <- true;

    (* weeding procedure *)
    while ( i < size bb){
      if (!ev1){
        b' <- nth witness bb i;
        ev1 <- b'.`2 = b.`2 /\ b'.`3 = b.`3; 
      }
      i <- i + 1;
    }
    (* check id and label from ballot *)
    if(uL.[b.`1] <> None){
      ev2 <- (oget uL.[b.`1]) = b.`2;
    }
    (* validInd procedure *)
    ev3 <@ C(H).validInd(b, pk);

    return (!ev1 /\ ev2 /\ ev3);
  }

  (* voting algorithm *)
  proc vote(id: ident, v: vote, l: label, pk: pkey): (ident * label * cipher) = {
    var c;

    c <@ E(H).enc(pk, l, v);
    return (id, l, c);
  }

  (* tally algorithm *)
  proc tally(bb: (ident * label * cipher) list, sk: skey): result * prf = {
    var ubb, b, i, m, pbb, pk, r, pi;

    ubb  <- [];
    i   <- 0;
    
    while( i < size bb){
      b  <- nth witness bb i;
      m  <@ E(H).dec(sk, b.`2, b.`3);
      ubb <- ubb ++ [(b.`1, m)];
      i  <- i + 1;
    }
    
    r     <$ Rho ubb;
    pbb   <- Publish (bb);
    pk    <- extractPk sk;
    pi <@ P(G).prove((pk, pbb, r), (sk, bb));

    return (r, pi);
  } 
  
  (* verify algorithm *)
  proc verify(st: (pkey * pubBB * result), pi: prf): bool = {
    var b;
    b <@ Ve(G).verify(st, pi);
    return b;
  }
}.

(* ---------------------------------------------------------------------- *)
(* experiments and constructed adversaries *)

(* zero-knowledge adversary that may query 2 random oracles:
   one from the encryption scheme, and one from the proof system *)
module type VotingAdvZK (H: HOracle.Oracle, O : GOracle.ARO) = {
  proc a1() : (pkey * pubBB * result) * 
              (skey * (ident * label * cipher) list) {H.init H.o O.o}
  proc a2(p : prf option) : bool {H.o O.o}
}.

(* Constructed ZK adversary from BPRIV adversary *)
module BZK(E: Scheme, P: Prover, C: ValidInd, Ve: Verifier, 
           A:BPRIV_Adv, H: HOracle.Oracle, G: GOracle.ARO) = {

  module O = BPRIV_Oracles(MV(E,P,Ve,C), H, G, Left)

  proc a1(): (pkey * pubBB * result) * 
             (skey * (ident * label * cipher) list) = {
    var m, b, id ;
    var ubb, pbb, i;
    
    i      <- 0;
    BP.qVo <- 0;
    BP.qCa <- 0;
    BP.bb0 <- [];
    BP.bb1 <- [];
    ubb    <- [];
    BP.uL  <- empty;

    
                     H.init();
    (BP.pk,BP.sk) <@ E(H).kgen(); 
    while (i< part){
      id    <$ d_ids;
      BP.uL.[id] <- Flabel(id);
      i     <- i + 1;
    }
                     A(O).a1(BP.pk, BP.uL);                 
    i <- 0;
    while (i < size BP.bb0){     
      b  <- nth witness BP.bb0 i;
      m  <@ E(H).dec(BP.sk, b.`2, b.`3);
      ubb <- ubb ++ [(b.`1,m)];
      i  <- i + 1;
    }
    BP.r  <$ Rho ubb;                
    pbb   <- Publish(BP.bb0);
    return ( (BP.pk, pbb, BP.r), (BP.sk, BP.bb0));
  }
  
  proc a2(pi: prf option ): bool = {
    BP.b <@ A(O).a2(BP.r, oget pi);
    return BP.b;
  }  
}.


(* Constructed VFR adversary from BPRIV adversary *)
module BVFR(V: VotingScheme, A:BPRIV_Adv, H:HOracle.ARO, G:GOracle.ARO) = {

  module L = BPRIV_Oracles(V, H, G, Left)

  proc main(pk: pkey): (ident * label * cipher) list={
    var i, id;
    i      <- 0;
    BP.qVo <- 0;
    BP.qCa <- 0;
    BP.bb0 <- [];
    BP.bb1 <- [];
    BP.uL  <- empty;
    BP.pk  <- pk;

    while (i < part){
      id    <$ d_ids;
      BP.uL.[id] <- Flabel(id);
      i     <- i + 1;
    }
    A(L).a1(BP.pk, BP.uL);
  return BP.bb0;
  }
}.

(* Intermediate game between GameL_BPRIV and GameR_BPRIV:
   adversary gets simulated proof, but uses left oracles *) 
module IBPRIV(V:VotingScheme, A:BPRIV_Adv, 
              H: HOracle.Oracle, G:GOracle.Oracle, S:Simulator) = {

  module O = BPRIV_Oracles(V, H, S, Left)
  module A = A(O)

  proc main() : bool = {
    var pbb, pi;

    BP.qVo <- 0;
    BP.qCa <- 0;
    BP.bb0 <- [];
    BP.bb1 <- [];
    BP.uL  <- empty;
    
                      H.init();
                      G.init();
                      S.init();
    (BP.pk, BP.sk, 
            BP.uL) <@ V(H,G).setup(part);
                      A.a1(BP.pk, BP.uL);
    (BP.r, BP.pi)  <@ V(H,G).tally(BP.bb0, BP.sk);
    pbb            <- Publish(BP.bb0);
    pi             <@ S.prove(BP.pk, pbb, BP.r);
    BP.b           <@ A.a2(BP.r, pi);
    return BP.b;
  }
}.

(* ---------------------------------------------------------------------- *)
(* BPRIV Game with sg board *)
module BPRIV_SB(E: Scheme, C: ValidInd,  A:BPRIV_Adv, 
                H: HOracle.Oracle, LR: LorR, S: BPRIV_Simulator) = {

  var bb  : (ident * label * cipher) list
  var hvo : (cipher * label, vote) map
  var encL: (cipher * label) list
  var badQ: int option

  (* MiniVoting Scheme: needed as we need the valid, 
                        and vote for simplicity *)
  module MV = {

    proc setup (n: int): pkey * skey * (ident, label) map = {
      var i, id, pk, sk,uL;
    
      i <- 0;
      uL <- empty;

      (pk, sk) <@ E(H).kgen();
      while (i < n){
        id    <$ d_ids;
        uL.[id] <- Flabel(id);
        i     <- i + 1;
      }
    
      return (pk, sk, uL);
    }
  
  
    proc valid (bb: (ident * label * cipher) list, 
                uL: (ident, label) map, 
                b : (ident * label * cipher),
                pk: pkey): bool = {

      var ev1, ev2, ev3;
      var b', i;

      i <- 0;
      ev1 <- false;
      ev2 <- false;
      ev3 <- true;

 
      while ( i < size bb){
        if (!ev1){
          b' <- nth witness bb i;
          ev1 <- b'.`2 = b.`2 /\ b'.`3 = b.`3; 
        }
        i <- i + 1;
      }

      if(uL.[b.`1] <> None){
        ev2 <- (oget uL.[b.`1]) = b.`2;
      }

      ev3 <@ C(H).validInd(b, pk);

      return (!ev1 /\ ev2 /\ ev3);
    }

    (* voting procedure *)
    proc vote(id: ident, v: vote, 
              l : label, pk: pkey): (ident * label * cipher) = {
      var c;

      c <@ E(H).enc(pk, l, v);
      return (id, l, c);
    }
  } (* MV ended *)



  (* BPRIV Oracles with sg board *)
  module O = {
    proc h = H.o
    proc g = S.o

    (* vote oracle *)
    proc vote(id : ident, v0 v1 : vote) : unit = {
      var b,v, l_or_r;
      var l, ev;
   
      if (BP.qVo < n){
        if (BP.uL.[id] <> None){
          l     <- oget BP.uL.[id]; 
          l_or_r <@ LR.l_or_r(); 
          v      <- l_or_r?v0:v1;
          b      <@ MV.vote(id, v, l, BP.pk);
          ev     <@ MV.valid(bb, BP.uL, b, BP.pk);
          if (ev) {
            bb  <- bb  ++ [b];
            hvo.[(b.`3, b.`2)] <- v0;
            encL<- encL++ [(b.`3,b.`2)];
          }elif(badQ = None){
            badQ <- Some BP.qVo;
          }
        }
        BP.qVo <- BP.qVo + 1;
      }
    }

    (* cast oracle *)
    proc cast(b : (ident * label * cipher)) : unit={
      var ev;

      if (BP.qCa < k ){
        ev <@ MV.valid(bb, BP.uL, b, BP.pk);
        if (ev){
          bb  <- bb  ++ [b];
        }
        BP.qCa <- BP.qCa + 1; 
      }
    }

    proc board(): pubBB={
      return Publish(bb);
    }
  }

  module A = A(O)

  proc main() : bool={
    var pbb, pi, i;
    var b, vo, ubb;

    BP.qVo  <- 0;
    BP.qCa  <- 0;
    i       <- 0;
    BP.uL   <- empty;
    bb      <- [];
    hvo     <- empty;
    ubb     <- [];
    encL    <- [];
    badQ    <- None;
                      H.init();
                      S.init();
    (BP.pk, BP.sk, 
            BP.uL) <@ MV.setup(part);
                      A.a1(BP.pk, BP.uL);

     while( i < size bb){ 
      b  <- nth witness bb i;

      if ( !mem encL (b.`3,b.`2)){
        vo <@ E(H).dec(BP.sk, b.`2, b.`3);
      }else{
        vo <- hvo.[(b.`3,b.`2)];
      }
      ubb <- ubb ++ [(b.`1, vo)];
      i  <- i + 1;
    }
    
    BP.r  <$ Rho ubb;
    pbb   <- Publish (bb);
    pi    <@ S.prove(BP.pk, pbb, BP.r);
    BP.b  <@ A.a2(BP.r, pi);

    return BP.b;
  }
}. 

(* ---------------------------------------------------------------------- *)
(* Hybrid section of definitions  *) 

(* IND1CCA adversary constructed from a BPRIV adversary,
   tally is computed based on decrypting cast ballots and 
         using saved v0 values (in hvo) for honest ballots (in encL), and
   badQ stores the first honest ballot that fails the valid algorithm *)
module BIND(V:VotingScheme, A: BPRIV_Adv, S: BPRIV_Simulator, IO: Ind1CCA_Oracles) ={

  var bb: (ident * label * cipher) list
  var hvo: (cipher * label, vote) map
  var badQ: int option
  var encL: (cipher * label) list

  module O = {

    proc h = IO.o
    proc g = S.o

    (* vote oracle *)
    proc vote(id : ident, v0 v1 : vote) : unit = {
      var b, c, l, ev;
   
      if (BP.qVo < n){
        if (BP.uL.[id] <> None){
          l   <- oget BP.uL.[id]; 
          (* challenge vote*)
          c    <@ IO.enc(l, v0, v1);
          encL <- encL++[(c,l)];
          b    <- (id, l, c);
          ev   <@ V(IO,S).valid(bb, BP.uL, b, BP.pk);
          if (ev) {
            bb  <- bb ++ [b];
            hvo.[(b.`3,b.`2)] <- v0;
          }elif(badQ = None){
            badQ <-Some BP.qVo;
          }
        }
        BP.qVo <- BP.qVo + 1;
      }
    }
  
    (* cast oracle *)
    proc cast(b : (ident * label * cipher)) : unit={
      var ev;
      
      if (BP.qCa < k){
        ev <@ V(IO,S).valid(bb, BP.uL, b, BP.pk);
        if (ev){
          bb <- bb ++ [b];         
        }
        BP.qCa <- BP.qCa + 1;
      }
    }

    (* public board *)
    proc board(): pubBB={
      return Publish(bb);
    }
  }(* end O module *)

  module A = A(O)

  proc main (pk: pkey): bool = {

    var i, id, pbb, pi, cL, mL;
    var b, vo, ubb;

    BP.qVo  <- 0;
    BP.qCa  <- 0;
    i       <- 0;
    BP.uL   <- empty;
    bb      <- [];
    hvo     <- empty;    
    encL    <- []; 
    badQ    <- None;     
    BP.pk   <- pk;              
    i <- 0;

    while (i <part){
      id    <$ d_ids;
      BP.uL.[id] <- Flabel(id);
      i     <- i + 1;
    }
    
    S.init();
    A.a1(BP.pk, BP.uL);

    i       <- 0;
    cL      <- [];
    mL      <- [];
    ubb     <- [];
    
    (* remove ID *)
    cL <- remID bb;

    (* decrypt all, with challenge to None *)
    mL <@ IO.dec(cL);

    while( i < size bb){ 
      b        <- nth witness bb i;

      if (!mem encL (b.`3,b.`2)){ (*C: replaced BS.encL by encL*)
       (* cast vote, use decryption from oracle *)
        vo   <- nth witness mL i;
      }else{
       (* honest vote, use vo saved *) 
        vo <- hvo.[(b.`3,b.`2)];
      }
      ubb <- ubb ++ [(b.`1, vo)];
      i  <- i + 1;
    }
    
    BP.r  <$ Rho ubb;
    pbb   <- Publish (bb);
    pi    <@ S.prove(BP.pk, pbb, BP.r);
    BP.b  <@ A.a2(BP.r, pi);
    return BP.b;
  }
}.

(* Similar to BIND, we create a IND1CCA andversary, but we use
   ibad to guess the exact position an honest ballot fails the valid algorithm,
        instead of setting the index badQ when it does, and update
   bad  with a boolean evaluation if we guessed correctly. *)
module BIND2(V:VotingScheme, A: BPRIV_Adv, S: BPRIV_Simulator, IO: Ind1CCA_Oracles) ={

  var bb: (ident * label * cipher) list
  var bad: bool
  var ibad: int

  module O = {

    proc h = IO.o
    proc g = S.o

    (* vote oracle *)
    proc vote(id : ident, v0 v1 : vote) : unit = {
      var b, c, l, ev;
   
      if(BP.qVo < n){
        if (BP.uL.[id] <> None){
          l   <- oget BP.uL.[id]; 
          (* challenge vote*)
          c    <@ IO.enc(l, v0, v1);
          b    <- (id, l, c);
          ev   <@ V(IO,S).valid(bb, BP.uL, b, BP.pk);
          if (ev) {
            bb  <- bb ++ [b];
          }
          if (!bad){
            bad <-!ev /\ BP.qVo = ibad; 
          }
        }
        BP.qVo <- BP.qVo + 1;
      }
    }
  
    (* cast oracle *)
    proc cast(b : (ident * label * cipher)) : unit={
      var ev;

      if (BP.qCa < k){
        ev <@ V(IO,S).valid(bb, BP.uL, b, BP.pk);
        if (ev){
          bb <- bb ++ [b];         
        }
        BP.qCa <- BP.qCa + 1;
      }
    }

    (* public board *)
    proc board(): pubBB={
      return Publish(bb);
    }
  }(* end BPRIVO module *)

  module A = A(O)

  proc main (pk: pkey): bool = {

    var i, id;
    ibad <$ [0..n-1];

    BP.qVo  <- 0;
    BP.qCa  <- 0;
    i       <- 0;
    BP.uL   <- empty;
    bb      <- [];    
    bad     <- false;     
    BP.pk   <- pk;              
    i <- 0;

    while (i < part){
      id    <$ d_ids;
      BP.uL.[id] <- Flabel(id);
      i     <- i + 1;
    }
    
    S.init();
    A.a1(BP.pk, BP.uL);
    return true;
  }
}.

(* strong correctness' adversary, that uses the guessed index
   ibad to call the test oracle to evaluate a honest ballot with the 
        valid algorithm *)
module BSCorr(V: VotingScheme, A: BPRIV_Adv, LR: LorR, SO: SCorr_Oracle) ={

  var bb: (ident * label * cipher) list
  var ibad: int

  module V = V(Hwrap(SO), Gwrap(SO))

  module O = {
    proc h = SO.h
    proc g = SO.g
    
    (* vote oracle *)
    proc vote(id : ident, v0 v1 : vote) : unit = {
      var b, l_or_r, v, l, ev;
    
      if (BP.qVo < ibad){
        (* call normal vote *)
        if (BP.uL.[id] <> None){
          l   <- oget BP.uL.[id]; 
          l_or_r <@ LR.l_or_r(); 
          v    <- l_or_r?v0:v1;
          b    <@ V.vote(id, v, l, BP.pk);
          ev   <@ V.valid(bb, BP.uL, b, BP.pk);
          if (ev) {
            bb  <- bb ++ [b];
          }
        }
        BP.qVo <- BP.qVo + 1;
      }elif (BP.qVo = ibad){
         (* call vote for bad event *)
         l_or_r <@ LR.l_or_r();
         v    <- l_or_r?v0:v1;
         SO.test(id,v,bb);
         BP.qVo   <- BP.qVo + 1;
       }
     }

    (* cast oracle *)
    proc cast(b : (ident * label * cipher)) : unit={
      var ev;
       
      if (BP.qCa < k){
        ev <@ V.valid(bb, BP.uL, b, BP.pk);
        if (ev){
          bb <- bb ++ [b];         
        }
        BP.qCa <- BP.qCa + 1;
      }
    }

    (* public board *)
    proc board(): pubBB={
      return Publish(bb);
    }
  }(* end O module *)

  module A = A(O)
  
  proc main(pk: pkey, uL: (ident, label) map): unit={
    ibad <$ [0..n-1];

    BP.qVo <- 0;
    BP.qCa <- 0;
    bb     <- [];
    BP.pk  <- pk;
    BP.uL  <- uL;
    A.a1(pk, uL); 
  }    

}.

(* ---------------------------------------------------------------------- *)
(* MiniVoting typecheck  *)
section.

  declare module E :Scheme.
  declare module P : Prover.
  declare module Ve: Verifier.
  declare module C : ValidInd.
  declare module O1: HOracle.Oracle.
  declare module O2: GOracle.Oracle.
  declare module V : VotingScheme.
  declare module S : Simulator.

  declare module A : BPRIV_Adv. 
  local module MS    = MV(E, P, Ve, C).
  local module M_LB  = BPRIV_Oracles(MS).
  local module M'_LB = IBPRIV(MS, A,O1,O2, S).
  local module BVF   = BVFR(MS,A).
  local module RS    = VFR(E, BVFR(MS,A)).
  local module B     = BZK(E,P,C,Ve, A, O1).

end section.