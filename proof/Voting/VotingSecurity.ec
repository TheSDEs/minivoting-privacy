require import Int Bool FMap DInterval.
require import List Distr Option.
require import LeftOrRight.
require (*  *) VotingDefinition.

clone include VotingDefinition.

(* * BPRIV security definition *)
(* ---------------------------------------------------------------------- *)

(* ** BPRIV oracles *)

(* BPRIV oracle types *)
module type BPRIV_Oracles = {
  (* rando oracles: for encryption and proof system *)
  proc h(inp: h_in)                      : h_out
  proc g(inp: g_in)                      : g_out

  (* voting oracles *)
  proc vote(id: ident, vo v1 : vote)     : unit
  proc cast(b: (ident * label * ballot)) : unit
  (* adversary view *)
  proc board()                           : pubBB
}.

(* Global state shared between BPRIV oracles and game *)
module BP = {
  var qVo : int
  var qCa : int
  var pk  : pkey
  var sk  : skey
  var r   : result
  var pi  : prf
  var b   : bool
  var bb0 : (ident * label * ballot) list
  var bb1 : (ident * label * ballot) list
  var uL  : (ident, label) map
}.

(* BPRIV Oracles *)
module BPRIV_Oracles(V: VotingScheme, 
                     H: HOracle.ARO, G: GOracle.ARO, 
                     LR: LorR): BPRIV_Oracles = {
  proc h = H.o
  proc g = G.o


  proc vote(id : ident, v0 v1 : vote) : unit = {
    var b0, b1, l_or_r;
    var ev, b, bb, l;
   
    if (BP.qVo < n) {
      if (BP.uL.[id] <> None) {
        l      <- oget BP.uL.[id];  
        b0     <@ V(H,G).vote(id, v0, l, BP.pk);
        b1     <@ V(H,G).vote(id, v1, l, BP.pk);
        l_or_r <@ LR.l_or_r();
        b      <- l_or_r?b0:b1;
        bb     <- l_or_r?BP.bb0:BP.bb1;
        ev     <@ V(H,G).valid(bb, BP.uL, b, BP.pk);
        if (ev) {
          BP.bb0  <- BP.bb0 ++ [b0];
          BP.bb1  <- BP.bb1 ++ [b1];
        }
      }
      BP.qVo <- BP.qVo + 1;
    }
  }
  
  proc cast(b : (ident * label * ballot)) : unit = {
    var ev, bb, l_or_r;

    if (BP.qCa < k){
      l_or_r <@ LR.l_or_r();
      bb   <- l_or_r?BP.bb0:BP.bb1;
      ev   <@ V(H,G).valid(bb, BP.uL, b, BP.pk);
      if (ev) {
        BP.bb0 <- BP.bb0 ++ [b];
        BP.bb1 <- BP.bb1 ++ [b];
      }
      BP.qCa <- BP.qCa + 1;
    }
  }

  proc board(): pubBB = {
    var l_or_r, bb;

    l_or_r <@ LR.l_or_r();
    bb     <- l_or_r?BP.bb0:BP.bb1;
    return Publish(bb);
  }
}.

(* ** BPRIV left *)

(* BPRIV adversary type *)
module type BPRIV_Adv(O: BPRIV_Oracles) = {
  proc a1 (pk: pkey, uL: (ident, label) map)           
          : unit { O.vote O.cast O.board O.h O.g}
  proc a2 (r: result, pi: prf) 
          : bool { O.board O.h O.g}
}.

(* Ballot privacy property: left side *)
module BPRIV_L(V: VotingScheme, A: BPRIV_Adv,  
               H: HOracle.Oracle, G: GOracle.Oracle) = {

  module O = BPRIV_Oracles(V, H, G, Left)
  module A = A(O)
  module V = V(H,G)

  proc main() : bool = {
    BP.qVo  <- 0;
    BP.qCa  <- 0;
    BP.bb0  <- [];
    BP.bb1  <- [];
    BP.uL   <- empty;

                      H.init();
                      G.init();
    (BP.pk, BP.sk, 
            BP.uL) <@ V.setup(part);
                      A.a1(BP.pk, BP.uL);
    (BP.r, BP.pi)  <@ V.tally(BP.bb0, BP.sk); 
    BP.b           <@ A.a2(BP.r, BP.pi);

    return BP.b;
  }
}.

(* BPRIV simulator type *)
module type BPRIV_Simulator = {
  proc init()          : unit
  proc o(x : g_in)     : g_out
  proc prove(st: (pkey * pubBB * result)) : prf 
}.

(* ** BPRIV right *)

(* Ballot privacy property: right side *)
module BPRIV_R(V: VotingScheme, A:BPRIV_Adv, 
               H: HOracle.Oracle, G: GOracle.Oracle, 
               S: BPRIV_Simulator) = {

  module O = BPRIV_Oracles(V, H, S, Right)
  module A = A(O)
  module V = V(H,G)

  proc main() : bool = {
    var pbb, pi;

    BP.qVo  <- 0;
    BP.qCa  <- 0;
    BP.bb0  <- [];
    BP.bb1  <- [];
    BP.uL   <- empty;
                      H.init();
                      G.init();
    (* init simul. *) S.init(); 
    (BP.pk, BP.sk, 
            BP.uL) <@ V.setup(part);
                      A.a1(BP.pk, BP.uL);
    (BP.r, BP.pi)  <@ V.tally(BP.bb0, BP.sk);
    (* start: simulate proof from public BB for BB1 *)
    pbb            <- Publish (BP.bb1);
    pi             <@ S.prove(BP.pk, pbb, BP.r);
    (* end *)
    BP.b           <@ A.a2(BP.r, pi);
    return BP.b;
  }
}.

(* * Strong consistency *)
(* ---------------------------------------------------------------------- *)

(* strong consistency op: extractor *)
module type Extractor(H: HOracle.ARO) = {
  proc extract(b: (ident * label * ballot), 
               sk: skey)
       : (ident * vote option)   {H.o}
}.

(* strong consistency op: validInd *)
module type ValidInd(H: HOracle.ARO) = {
  proc validInd(b: (ident * label * ballot), 
                pk: pkey)
       : bool  {H.o}
}.

(* strong consistency oracle type *)
module type SCons_Oracle = {
  proc h(inp: h_in) : h_out
  proc g(inp: g_in) : g_out
}.

(* strong consistency oracle instantiation *)
module SCons_Oracle(V: VotingScheme, 
                    H: HOracle.ARO, G: GOracle.ARO) = {
  proc h = H.o
  proc g = G.o
}.

(* strong correctness oracle type *)
module type SCorr_Oracle = {
  (* random oracles *)
  proc h(inp: h_in) : h_out
  proc g(inp: g_in) : g_out
  (* strong correctness test *)
  proc test(id:ident, v: vote,
            bb: (ident * label * ballot) list)
       : unit
}.

(* Global state shared between strong consistency/correctness oracles and game *)
module BSC = {
  var uL    : (ident, label) map
  var valid : bool
  var qt    : int
  var pk    : pkey
}.

(* strong correctness oracle instantiation *)
module SCorr_Oracle(V: VotingScheme, 
                    H: HOracle.ARO, G: GOracle.ARO) = {
  proc h    = H.o
  proc g    = G.o
  
  proc test(id: ident, v: vote, 
            bb: (ident * label * ballot) list): unit = {
    var l, b, l', ev;

    if (BSC.qt < 1){   
      if (size bb < n + k){
        l <- BSC.uL.[id];
        if (l <> None){
          l'   <- oget l; 
          b    <@ V(H,G).vote(id, v, l', BSC.pk);
          ev   <@ V(H,G).valid(bb, BSC.uL, b, BSC.pk);
          if(!BSC.valid){
            BSC.valid <- !ev;  
          }
        }
      }
      BSC.qt <- BSC.qt + 1;
    }
  }
}.

(* a similar definition for strong correctness, but without restriction 
   on the number of calls to the test oracle *)
module SCorr_Oracle' (V: VotingScheme, 
                      H: HOracle.ARO, G: GOracle.ARO) = {
  proc h    = SCorr_Oracle(V,H,G).h
  proc g    = SCorr_Oracle(V,H,G).g

  proc test(id: ident, v: vote, 
            bb: (ident * label * ballot) list): unit = {
    var l, b, l', ev;

    ev <- true;
    if (size bb < n + k){
      l <- BSC.uL.[id];
      if (l <> None){
        l'   <- oget l; 
        b    <@ V(H,G).vote(id, v, l', BSC.pk);
        ev   <@ V(H,G).valid(bb, BSC.uL, b, BSC.pk);
      }
    }
    BSC.qt <- BSC.qt + 1;
    if(!BSC.valid){
      BSC.valid <- !ev;
    }
  }
}.

(* 2. strong consistency part 1 *)
module SConsis1(V: VotingScheme, C: Extractor, 
                H: HOracle.Oracle, G: GOracle.Oracle) = {
  module V = V(H, G)
  module C = C(H)

  proc main (id: ident, v: vote, l: label ): bool = {
    var b, i, id', v';

    i       <- 0;
    BP.uL   <- empty;
                      H.init();
                      G.init();
    (BP.pk, BP.sk, 
            BP.uL) <@ V.setup(part);
    (* Extract of Vote  give id and vote *) 
    b              <@ V.vote(id, v, l, BP.pk);
    (id',v')       <@ C.extract(b, BP.sk);
    BP.b           <- (id' = id) /\ (v' =  Some v);
  
    return BP.b;
  }
}.

(* Strong Consistency part 2 adversary *)
module type SConsis2_Adv(O:SCons_Oracle) = {
  proc main(pk: pkey, uL: (ident, label) map)
       : (ident * label * ballot) list * (ident * label * ballot)
}.

(* 2. strong consistency part 2 *)
module SConsis2(V:VotingScheme, 
                C:ValidInd, A:SConsis2_Adv, 
                H: HOracle.Oracle, G:GOracle.Oracle) = {
 
  module O = SCons_Oracle(V, H, G)
  module V = V(H,G)
  module A = A(O)

  proc main (): bool = {
    var bb, b, b';
    
    bb      <- [];
    BP.uL   <- empty;
                      H.init();
                      G.init();
    (BP.pk, BP.sk, 
            BP.uL) <@ V.setup(part);
    (bb, b)        <@ A.main(BP.pk, BP.uL);
    (* Valid implies validInd *)
    BP.b           <@ V.valid(bb, BP.uL, b, BP.pk);
    
    b'             <@ C(H).validInd(b, BP.pk);
    return (!BP.b || b');
  }
}.

(* Strong consistency part 3 adversary *)
module type SConsis3_Adv(O:SCons_Oracle) = {
  proc main (pk: pkey, uL: (ident, label) map)
       : (ident * label * ballot) list
}.


(* 2. strong consistency part 3 left experiment *)
module SConsis3_L(V: VotingScheme, 
                  C2:ValidInd, A: SConsis3_Adv, 
                  H: HOracle.Oracle, G:GOracle.Oracle) = {
  module O = SCons_Oracle(V, H, G)
  module V = V(H, G)
  module A = A(O)

  proc main (m:int) : result option = {
    var bb, ev, i, b, r;

    i       <- 0;
    ev      <- true;
    bb      <- [];
    BP.uL   <- empty;
                      H.init();
                      G.init();
    (BP.pk, BP.sk, 
            BP.uL) <@ V.setup(part);
    bb             <@ A.main(BP.pk, BP.uL);

    while (i < size bb){
      b <- nth witness bb i;
      if (ev){
        ev <@ C2(H).validInd(b, BP.pk);
      }
      i <- i + 1;
    }

    (* compute result by tally *)
    r <- None;
    if (ev){
      (BP.r, BP.pi) <@ V.tally(bb, BP.sk);
      r             <- Some BP.r;
    }

    return r;
  }
}.

(* 2. strong consistency part 3 right experiment *)
module SConsis3_R(V: VotingScheme, C1:Extractor, 
                  C2:ValidInd, A: SConsis3_Adv, 
                  H: HOracle.Oracle, G: GOracle.Oracle) = {
  module O = SCons_Oracle(V, H, G)
  module V = V(H, G)
  module A = A(O)

  proc main () : result option = {
    var bb, ub, ev, i, b, m', r, r';

    i       <- 0;
    ev      <- true;
    bb      <- [];
    ub      <- [];
    BP.uL   <- empty;
                      H.init();
                      G.init();
    (BP.pk, BP.sk, 
            BP.uL) <@ V.setup(part);
    bb             <@ A.main(BP.pk, BP.uL);

    while (i < size bb){
      b <- nth witness bb i;
      if (ev){
        ev <@ C2(H).validInd(b, BP.pk);
      }
      i <- i + 1;
    }

    (* compute result by rho over Extract *)
    r <- None;
    if (ev){
      i <- 0;
      while (i < size bb){
        b  <- nth witness bb i;
        m' <@ C1(H).extract(b, BP.sk);
        ub <- ub ++ [m'];
        i <- i + 1;
      }
      r' <$ Rho ub;
      r <- Some r';
    }

    return r;
  }
}.

(* Strong correctness adversary *)
module type SCorr_Adv(O:SCorr_Oracle) = {
  proc main(pk: pkey, uL: (ident, label) map) : unit
}.

(* strong correctness experiment *)
module SCorr(V:VotingScheme, A: SCorr_Adv, 
             H: HOracle.Oracle, G: GOracle.Oracle) = {
  module O = SCorr_Oracle(V, H, G)
  module V = V(H, G)
  module A = A(O)
  
  proc main () : bool = {
    var sk;

    BSC.uL    <- empty;
    BSC.valid <- false;
    BSC.qt    <- 0;

                    H.init();
                    G.init();
    (BSC.pk, sk, 
         BSC.uL) <@ V.setup(part);
                   A.main(BSC.pk, BSC.uL);

    return BSC.valid;
  }
}.

(* strong correctness' experiment *)
module SCorr'(V:VotingScheme, A: SCorr_Adv,
             H: HOracle.Oracle, G: GOracle.Oracle) = {
  module O = SCorr_Oracle'(V, H, G)
  module V = V(H, G)
  module A = A(O)
  
  proc main () : bool = {
    var sk;

    BSC.uL    <- empty;
    BSC.valid <- false;
    BSC.qt    <- 0;

                    H.init();
                    G.init();
    (BSC.pk, sk, 
         BSC.uL) <@ V.setup(part);
                    A.main(BSC.pk, BSC.uL);
    

    return BSC.valid;
  }
}.

(* ---------------------------------------------------------------------- *)
(* strong correctness' adversary that has access a voting scheme *)
module type SCorr_Adv' (V : VotingScheme, O : SCorr_Oracle) = {
  proc main(pk: pkey, uL : (ident,label) map) : unit {O.h O.g O.test}
}.

(* strong correctness  experiment is indistinguishable from
   strong correctness' experiment under the assumption that the
   adversary makes at most one query for the test oracle *)
section ScorrReduction.
  require import Real.

  declare module H  : HOracle.Oracle {BSC}.
  declare module G  : GOracle.Oracle {BSC, H}.
  declare module V  : VotingScheme   {BSC, H, G}.
  declare module AC : SCorr_Adv'     {BSC, H, G, V}.

  (* extract the H.o oracle from the strong correctness oracles *)
  module Hwrap(SO: SCorr_Oracle) = {
    proc o    = SO.h
  }.
  (* extract the G.o oracle from the strong correctness oracles *)
  module Gwrap(SO: SCorr_Oracle) = {
    proc o   = SO.g
  }.

(* ** ASSUMPTIONS ** *)
(* ** start *)
  (* Strong correctness' adversary makes at most 1 query: BSC.qt<=1 *)
  axiom AC_bound (uL: (ident,label) map) (pk:pkey) &m : 
    BSC.uL{m} = uL /\ BSC.qt{m} =0 =>
    Pr[AC(V,SCorr_Oracle'(V,H,G)).main(pk, uL) @ &m: BSC.qt <=1] = 1%r. 

  (* lossless *)
  axiom AC_ll (V <: VotingScheme{AC}) (O <: SCorr_Oracle {AC}):
    islossless O.h => 
    islossless O.g => 
    islossless O.test =>
    islossless AC(V,O).main.
  
  axiom H_ll: islossless H.o.
  axiom G_ll: islossless G.o.

  axiom Vvot_ll (H<: HOracle.ARO) (G<: GOracle.ARO):
    islossless H.o =>
    islossless G.o =>
    islossless V(H,G).vote.

  axiom Vval_ll (H<: HOracle.ARO) (G<: GOracle.ARO):
    islossless H.o =>
    islossless G.o =>
    islossless V(H,G).valid.
(* ** end *)    
  
  (* *)
  hoare hl_AC_bounded: AC(V,SCorr_Oracle'(V, H, G)).main: BSC.uL = arg.`2 /\
                                                          BSC.qt = 0 ==> BSC.qt <= 1.
  proof.
    hoare.
    phoare split ! 1%r 1%r=> //=.
      conseq (AC_ll V (SCorr_Oracle'(V,H,G)) _ _ _).
      + by conseq H_ll.
      + by conseq G_ll.
      + proc. 
        sp; if => //=; last by auto. 
        sp; if => //=; last by auto. 
        wp; call (Vval_ll H G H_ll G_ll). 
        by call (Vvot_ll H G H_ll G_ll); wp.
    by bypr => &m Hqt; rewrite (AC_bound uL{m} pk{m} &m Hqt). 
  qed.

  (* strong correctness is indistinguishable from
     strong correctness' *)
  lemma SCorr_vers &m:
    Pr[SCorr (V,AC(V),H,G).main() @ &m: BSC.valid]=
    Pr[SCorr'(V,AC(V),H,G).main() @ &m: BSC.valid].
  proof.
  byequiv=>//.
  proc.
  conseq (_: ={glob AC, glob H, glob G, glob V} ==> BSC.qt{2} <=1 => ={BSC.valid})
         _ (_: true ==> BSC.qt <= 1); first 2 by smt.
    call hl_AC_bounded.
    wp; call (_: true).
    call(_: true); call(_: true). 
    by auto.

  call(_: !BSC.qt <= 1
          ,={glob H, glob G, glob V, BSC.uL, BSC.valid, BSC.qt, BSC.pk}/\
           0 <= BSC.qt{2}
          )=>//=.
   + exact AC_ll.     
   + proc ( BSC.qt{2} <= 1 /\ 
            ={glob G, glob V, BSC.uL, BSC.valid, BSC.qt, BSC.pk} /\
            0 <= BSC.qt{2}); progress. 
   + progress; by conseq H_ll. 
   + progress; by conseq H_ll.
   + proc ( BSC.qt{2} <= 1 /\ 
            ={glob H, glob V, BSC.uL, BSC.valid, BSC.qt, BSC.pk} /\
            0 <= BSC.qt{2}); progress.
   + progress; by conseq G_ll. 
   + progress; by conseq G_ll. 
   + proc. 
     sp; if{1}=>//=.
       if=>//=; last by auto; progress; smt.
       sp; if=>//=; last by auto; progress; smt. 
       wp; call (_: ={glob H}).
         by sim.
       call(_: ={glob H}).
         by sim. 
       by auto; progress; smt. 
     if{2} =>//=; last by auto; smt.
     sp; if{2} =>//=; last by auto; smt.
     wp; call{2} (Vval_ll H G H_ll G_ll).
     call{2} (Vvot_ll H G H_ll G_ll).
     by auto; progress; smt.     
   + progress; proc.   
     sp; if=>//=.
     wp; sp; if=>//=.
     sp; if=>//=. 
     wp; call (Vval_ll H G H_ll G_ll).
     call (Vvot_ll H G H_ll G_ll).
     by auto. 
   + proc.
     sp; if=>//=; last by auto; progress; smt. 
     sp; if=>//=; last by auto; progress; smt.     
     wp; call (Vval_ll H G H_ll G_ll).
     call (Vvot_ll H G H_ll G_ll).
     by auto; progress; smt. 

  call(_: ={glob H}).
  call(_: true); call(_: true). 
  by auto; progress; smt.
qed.
end section ScorrReduction.

(* Typecheck section *)
section.
  require import Real.

  declare module H : HOracle.Oracle.
  declare module G : GOracle.Oracle.
  declare module V : VotingScheme.
  declare module Si: BPRIV_Simulator.
  declare module CE: Extractor.
  declare module CV: ValidInd.

  declare module AB : BPRIV_Adv.
  declare module AC2: SConsis2_Adv. 
  declare module AC3: SConsis3_Adv. 
  declare module AC : SCorr_Adv.

  (* Advantage typecheck *)

  (* BPRIV *)
  local lemma bpriv &m: 
    exists eps,
      `| Pr[BPRIV_L(V, AB, H, G ).main() @ &m: res] -
         Pr[BPRIV_R(V, AB, H, G, Si).main() @ &m: res] | <= eps by [].

  (* Strong consistency *)
  local lemma consis1(id: ident, v: vote, l: label) &m: 
    exists eps, 0%r < eps /\
     Pr[SConsis1(V, CE, H, G).main(id,v, l) @ &m: res]  >= 1%r - eps by [].

  local lemma consis2 &m: 
    exists eps, 0%r < eps /\
    Pr[SConsis2(V, CV, AC2, H, G).main() @ &m: res] >= 1%r - eps by [].

  local equiv consis3 &m:
    SConsis3_L(V, CV, AC3, H, G).main ~ 
    SConsis3_R(V, CE, CV, AC3, H, G).main
    : ={glob H, glob G, glob V, glob CV, glob AC3} ==> ={res} by admit.

  (* Strong correctness *)
  local lemma corr &m: 
    exists eps, 0%r < eps /\
      Pr[SCorr(V, AC, H, G).main() @ &m: BSC.valid]  < eps by [].
end section.
