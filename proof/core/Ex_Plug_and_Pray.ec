(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)
require import Pair Int Real Distr DInterval.

(* 
  TODO:
    - Generalize from Dinter to Duni.
    - Provide another version for arbitrary distributions where the
      probability is upper-bounded by maximum probability of element
      in support of distribution.
*)

type tin.
type tres.

const bound : { int | 0 < bound } as bound_pos.

module type Game = {
  proc main(x:tin): tres
}.

module Guess(G:Game) = {  
  proc main(x:tin): int * tres = {
    var i, o;

    i = $[0..bound - 1]; (* swapped  *)
    o = G.main(x);
    return (i,o);
  }
}.

lemma PBound (G <: Game) phi psi x0 &m:
  (1%r/bound%r) * Pr[G.main(x0) @ &m: phi (glob G) res]
  = Pr[Guess(G).main(x0) @ &m:
         phi (glob G) (snd res) /\
         let k = psi (glob G) (snd res)  in
         fst res = if 0 <= k < bound then k else 0].
proof.
  rewrite eq_sym.
  byphoare (_: (glob G) = (glob G){m} /\ x0 = x ==>
               phi (glob G) (snd res) /\
               let k = psi (glob G) (snd res) in
               fst res = if 0 <= k < bound then k else 0) => //.
  pose p:= Pr[G.main(x0) @ &m: phi (glob G) res].
  proc.
  swap 1.
  seq  1: (phi (glob G) o)
          (p) (1%r/bound%r)
          _ 0%r => //.
    (* probability equality for 'phi (glob G) o' *)
    call (_:  (glob G) = (glob G){m} && x = x0 ==> phi (glob G) res) => //.
    bypr; progress; rewrite /p.
    byequiv (_: (glob G){1} = (glob G){2} /\ x{1} = x{2} ==>
                (phi (glob G) res){1} = (phi (glob G) res){2}) => //.
      by proc true.
    smt.
    (* probability of sampling such that Guess.i = psi (glob G) o *)
    rnd; skip; progress.
    rewrite /fst /snd /=.
    cut ->: (fun x,
              phi (glob G){hr} o{hr} /\
              x = if 0 <= psi (glob G){hr} o{hr} < bound
                    then psi (glob G){hr} o{hr}
                    else 0)
            = (pred1  (if 0 <= psi (glob G){hr} o{hr} < bound
                       then psi (glob G){hr} o{hr}
                       else 0)).
      by apply fun_ext=> x //=; rewrite H /= (eq_sym x).
    rewrite -/(mu_x _ _) mux_dinter. 
    progress. 
    have ->: (bound - 1 + 1) = bound by smt.
    case (0 <= psi (glob G){hr} o{hr} < bound). 
    + have Hneed: forall (a b: int), a< b => a<= b-1 
      by progress; rewrite -(lez_add2r 1 _ _) //=; smt. 
      smt.
    + smt.
    (* probability that sampling changes '!phi (glob G) o' to 'phi (glob G) o' zero *)
    hoare; rnd; skip; progress [-split].
    by move: H; rewrite -neqF /snd /= => ->.
qed.
