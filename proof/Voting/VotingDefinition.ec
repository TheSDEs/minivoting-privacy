require import Int Bool List Distr Option FMap.
require import LeftOrRight.
require (*  *) ROM.

(* * Types and operators for voting scheme *)
(* ---------------------------------------------------------------------- *)

type ident.  (* voter identifiers *)
type vote.   (* vote *)
type result. (* result *)
type ballot. (* ballot *)
type pubBB.  (* public bulletin box *)
type label.  (* label *)
type pkey.   (* election public key *)
type skey.   (* election secret key *)
type prf.    (* proof *)

op Rho     : (ident * vote option) list -> result distr. 
op Publish : (ident * label * ballot) list -> pubBB.

(* bound on the number of participants *)
op part: {int | 0 < part} as part_pos.
(* bound on the number of honest ballots that pass valid : BP.qVo < n *)
op n : { int | 0 < n} as n_pos.
(* bound on the number of cast ballots that pass valid : BP.qCa < k *)
op k : { int | 0 < k} as p_pos.
(* bound on the size of the bulletin board used in strong correctness:
   size bb < n + k *)

(* * Random oracles for voting scheme *)
(* ---------------------------------------------------------------------- *)

type h_in, h_out. (* input and output for random oracle H used for ballot *)
type g_in, g_out. (* input and output for random oracle G used for proof  *)

op dh_out : h_out distr.
op dg_out : g_out distr.

(** TODO: beware the hidden distribution and axiomatization **)
(*  NOTE: random oracle for voting cannot be simulated*) 
clone ROM.Types as HOracle with
  type from            <- h_in,
  type to              <- h_out,
  op dsample(x: h_in) <- dh_out.

(** TODO: beware the hidden distribution and axiomatization **)
(* random oracle that can be simulated *) 
clone ROM.Types as GOracle with
  type from            <- g_in,
  type to              <- g_out,
  op dsample(x: g_in) <- dg_out.

(* * Voting scheme syntax *)
(* ---------------------------------------------------------------------- *)

module type VotingScheme(H: HOracle.ARO, G: GOracle.ARO) = {
  proc setup(n: int)                                                 
    : pkey * skey * (ident, label) map                    { }
  proc vote(id: ident, v: vote, lbl: label, pk: pkey)
    : (ident * label * ballot)                            {H.o}
  proc valid(bb: (ident * label * ballot) list, 
             uL: (ident, label) map, 
             b : (ident * label * ballot),
             pk: pkey)
    : bool                                                {H.o}
  proc tally(bb: (ident * label * ballot) list, sk: skey)
    : result * prf                                        {H.o G.o}
  proc verify(st: (pkey * pubBB * result), pi: prf) 
    : bool                                                {G.o}
}.
