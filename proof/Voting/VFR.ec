require import Int Real FMap.
require import List Distr Option.
require (*  *) LPKE ProofSystem.


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

(* operators *)
op dh_out : h_out distr.   (* distribution for random oracle H *)
op dg_out : g_out distr.   (* distribution for random oracle G *)

(* result function rho *)
op Rho    : (ident * vote option) list -> result distr.
(* public algorithm Publish *)
op Publish: (ident * label * cipher) list  -> pubBB.  
(* bound nr of challenge queries *)
op n : { int | 0 < n } as n_pos.   

(* import encryption scheme *) 
clone export LPKE as PKEvf with
  type label  <- label,
  type plain  <- vote,
  type cipher <- cipher,
  type pkey   <- pkey,
  type skey   <- skey,
  type h_in   <- h_in,
  type h_out  <- h_out,
  op   dout   <- dh_out,
  op   n      <- n
  proof *.
  realize n_pos. by apply n_pos. qed.

(* import proof system *)
clone export ProofSystem as PSvf with
  type stm   <- pkey  * pubBB * result,
  type wit   <- skey * (ident * label * cipher) list,
  type prf   <- prf,
  type g_in  <- g_in,
  type g_out <- g_out,
  op   dout  <- dg_out
  proof *. 


(* ---------------------------------------------------------------------- *)
(* Voting friendly relation security definitions *)

(* VFR adversary *)
module type VFR_Adv(H: PKEvf.ARO, G: PSvf.ARO) ={
  proc main(pk: pkey)  : (ident * label * cipher) list { H.o G.o} 
}.

(* voting relation that may query the random oracle 
   of the encryption scheme given as input *)
module type VotingRelation (H: PKEvf.ARO) (*: Relation*) ={
  proc main(w: (pkey * pubBB * result), 
            s: (skey * (ident * label * cipher) list)): bool 
}.

module type VotingRelation' (E: Scheme, H: PKEvf.ARO) (*: Relation*) ={
  proc main(w: (pkey * pubBB * result), 
            s: (skey * (ident * label * cipher) list)): bool 
}.
  

(* 1. VFR experiment *) 
module VFR(E:Scheme, A:VFR_Adv, R: VotingRelation, H: PKEvf.Oracle, G: PSvf.Oracle )={

  proc main():bool={
    var r, i, b, m, rel;
    var bb, ubb, pbb;

    i   <- 0;
    ubb <- [];
    bb  <- [];
    
    H.init();
    G.init();
    (BS.pk,BS.sk) <@ E(H).kgen();
    bb      <@ A(H,G).main(BS.pk); 
    
    while (i < size bb){
      b    <- nth witness bb i;
      m    <@ E(H).dec(BS.sk, b.`2, b.`3);
      ubb  <- ubb ++[(b.`1,m)];     
      i    <- i + 1;
    }

    r <$ Rho ubb;                              
    pbb <- Publish bb;   
    rel <@ R(H).main((BS.pk, pbb, r), (BS.sk, bb));
    return !rel;
  }
}.


(* * * * * * * * * * * * * * * * * * * *
 * * * * * Advantage typecheck * * * * *)
(*module type VFR_rel (H: PKEvf.ARO) = {
  proc main(s : pkey * pubBB * result, 
            w : skey * (ident * label * cipher) list) : bool {H.o} 
}.*)

section.
  declare module S : Scheme.
  declare module R : VotingRelation'.
  (*declare module R': VFR_rel.*)
  declare module H : PKEvf.Oracle.
  declare module G : PSvf.Oracle.
  declare module A : VFR_Adv. 

  local lemma rel &m: 
    exists eps, 0%r < eps /\
      Pr[ VFR(S,A,R(S),H,G).main() @ &m: res] < eps by [].

end section.
