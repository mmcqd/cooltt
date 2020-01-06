module CS = ConcreteSyntax
module S = Syntax
module D = Domain
module Env = ElabEnv
module Err = ElabError
module EM = ElabBasics
module R = Refiner

open CoolBasis
open Monad.Notation (EM)

let rec chk_tp : CS.t -> S.tp EM.m = 
  function
  | CS.Pi (cells, body) -> 
    nary_quantifier R.Pi.formation cells body
  | CS.Sg (cells, body) -> 
    nary_quantifier R.Sg.formation cells body
  | CS.Id (tp, l, r) ->
    R.Id.formation (chk_tp tp) (chk_tm l) (chk_tm r)
  | CS.Nat -> 
    EM.ret S.Nat
  | tp -> 
    EM.elab_err @@ Err.InvalidTypeExpression tp

and chk_tm : CS.t -> D.tp -> S.t EM.m =
  function
  | CS.Hole name ->
    R.unleash_hole name
  | CS.Refl ->
    R.Id.intro 
  | CS.Lit n ->
    R.Nat.literal n
  | CS.Lam (BN bnd) ->
    R.tac_multilam bnd.names @@ chk_tm bnd.body
  | CS.Pair (c0, c1) ->
    R.Sg.intro (chk_tm c0) (chk_tm c1)
  | CS.Suc c ->
    R.Nat.suc (chk_tm c)
  | CS.Let (c, B bdy) -> 
    R.tac_let (syn_tm c) (Some bdy.name, chk_tm bdy.body)
  | cs ->
    R.syn_to_chk @@ syn_tm cs

and syn_tm : CS.t -> (S.t * D.tp) EM.m = 
  function
  | CS.Var id -> 
    R.lookup_var id
  | CS.Ap (t, ts) ->
    R.tac_multi_apply (syn_tm t) begin
      ts |> List.map @@ fun (CS.Term cs) ->
      chk_tm cs
    end
  | CS.Fst t ->
    R.Sg.pi1 @@ syn_tm t
  | CS.Snd t ->
    R.Sg.pi2 @@ syn_tm t
  | CS.IdElim {mot = B3 mot; case_refl = B case_refl; scrut} ->
    R.Id.elim 
      (Some mot.name1, Some mot.name2, Some mot.name3, chk_tp mot.body) 
      (Some case_refl.name, chk_tm case_refl.body) 
      (syn_tm scrut)
  | CS.NatElim {mot = B mot; case_zero; case_suc = B2 case_suc; scrut} ->
    R.Nat.elim 
      (Some mot.name, chk_tp mot.body)
      (chk_tm case_zero)
      (Some case_suc.name1, Some case_suc.name2, chk_tm case_suc.body)
      (syn_tm scrut)
  | CS.Check {term; tp} ->
    R.chk_to_syn (chk_tm term) (chk_tp tp)
  | cs -> 
    failwith @@ "TODO : " ^ CS.show cs

and nary_quantifier tac cells body =
  match cells with
  | [] -> chk_tp body
  | Cell cell :: cells ->
    tac (chk_tp cell.tp) (Some cell.name, nary_quantifier tac cells body)