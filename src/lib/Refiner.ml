module D = Domain
module S = Syntax
module CS = ConcreteSyntax
module Env = ElabEnv
module Err = ElabError
module EM = ElabBasics

open CoolBasis
open Monads
open Monad.Notation (EM)
open Bwd

type tp_tac = S.tp EM.m
type chk_tac = D.tp -> S.t EM.m
type syn_tac = (S.t * D.tp) EM.m
type dim_tac = S.dim EM.m

type ('a, 'b) quantifier = 'a -> CS.ident option * 'b -> 'b

let rec int_to_term =
  function
  | 0 -> S.Zero
  | n -> S.Suc (int_to_term (n - 1))

module Hole =
struct
  let make_hole name flexity tp = 
    let rec go_tp : Env.cell list -> S.tp m =
      function
      | [] ->
        EM.lift_qu @@ Nbe.quote_tp @@ D.Tp (D.GoalTp (name, tp))
      | `Con cell :: cells ->
        let ctp, _ = Env.Cell.contents cell in
        let name = Env.Cell.name cell in
        let+ base = EM.lift_qu @@ Nbe.quote_tp ctp
        and+ fam = EM.push_var name ctp @@ go_tp cells in
        S.Tp (S.Pi (base, fam))
      | `Dim cell :: cells -> 
        let+ fam = EM.push_dim_var name @@ go_tp cells in
        S.Tp (S.DimPi fam)
      | `Cof _ :: _ -> 
        failwith "Not supported yet"
      | `Prf _ :: _ -> 
        failwith "Not supported yet"
    in

    let rec go_tm cut : Env.cell bwd -> D.cut =
      function
      | Emp -> cut
      | Snoc (cells, `Con cell) ->
        let tp, con = Env.Cell.contents cell in
        go_tm cut cells |> D.push @@ D.KAp (tp, con) 
      | Snoc (cells, `Dim cell) ->
        let r = Env.Cell.contents cell in
        go_tm cut cells |> D.push @@ D.KDimAp r
      | Snoc (_, `Cof _) ->
        failwith "Not supported yet"
      | Snoc (_, `Prf _) ->
        failwith "Not supported yet"
    in

    let* env = EM.read in
    let names = Pp.Env.names @@ Env.pp_env env in
    EM.globally @@
    let+ sym =
      let* tp = go_tp @@ Bwd.to_list @@ Env.locals env in
      let* () =
        () |> EM.emit @@ fun fmt () ->
        Format.fprintf fmt "Emitted hole:@,  @[<v>%a@]@." (S.pp_sequent ~names) tp
      in
      let* vtp = EM.lift_ev @@ Nbe.eval_tp tp in
      match flexity with
      | `Flex -> EM.add_flex_global vtp
      | `Rigid -> EM.add_global name vtp None
    in

    D.push D.KGoalProj @@ go_tm (D.Global sym, []) @@ Env.locals env 

  let unleash_hole name flexity : chk_tac =
    fun tp ->
    let* cut = make_hole name flexity tp in 
    EM.lift_qu @@ Nbe.quote_cut cut

  let unleash_tp_hole name flexity : tp_tac =
    let* cut = make_hole name flexity @@ D.Tp D.Univ in 
    EM.lift_qu @@ Nbe.quote_tp (D.Tp (D.El cut))

  let unleash_syn_hole name flexity : syn_tac =
    let* tpcut = make_hole name `Flex @@ D.Tp D.Univ in 
    let+ tm = unleash_hole name flexity @@ D.Tp (D.El tpcut) in
    tm, D.Tp (D.El tpcut)
end


module Goal = 
struct
  let formation lbl tac =
    let+ tp = tac in
    S.Tp (S.GoalTp (lbl, tp))
end


module type TypeGoal =
sig
  type tac
  type goal
  type tp

  val make : (goal -> tp EM.m) -> tac
  val run : goal -> tac -> tp EM.m

  val eval_tp : tp -> D.tp EM.m

  val tp : tp S.gtp -> tp 
end

module TypeGoalTp : TypeGoal with type tac = tp_tac = 
struct 
  type goal = unit
  type tp = S.tp
  type tac = tp_tac

  let make tac = tac ()
  let run _ tac = tac

  let eval_tp tp =
    EM.lift_ev @@ Nbe.eval_tp tp

  let tp tp = S.Tp tp
end

module TypeGoalCode : TypeGoal with type tac = chk_tac = 
struct
  type goal = D.tp
  type tp = S.t 
  type tac = chk_tac

  let dest_univ =
    function
    | D.Tp D.Univ -> EM.ret ()
    | tp -> EM.elab_err @@ Err.ExpectedConnective (`Univ, tp)

  let make tac = 
    fun univ ->
    let* () = dest_univ univ in
    tac univ

  let run tp tac = tac tp

  let eval_tp tp =
    EM.lift_ev @@ Nbe.eval_tp @@ S.Tp (S.El tp)

  let tp tp = S.TpCode tp
end

module FormationRules (G : TypeGoal) : 
sig
  val nat : G.tac
  val pi : G.tac -> CS.ident option * G.tac -> G.tac
  val gen_pi : [`Dim | `Tp of G.tac] -> CS.ident option * G.tac -> G.tac
  val sg : G.tac -> CS.ident option * G.tac -> G.tac
  val id : G.tac -> chk_tac -> chk_tac -> G.tac
  val dim_pi : CS.ident option * G.tac -> G.tac
end = 
struct 
  let nat =
    G.make @@ fun _ ->
    EM.ret @@ G.tp S.Nat

  let family tac_base (nm, tac_fam) goal =
    let* base = G.run goal tac_base in
    let* vbase = G.eval_tp base in
    let+ fam = EM.push_var nm vbase @@ G.run goal tac_fam in 
    base, fam

  let pi (tac_base : G.tac) (nm, tac_fam) : G.tac = 
    G.make @@ fun goal ->
    let+ base, fam = family tac_base (nm, tac_fam) goal in
    G.tp @@ S.Pi (base, fam)

  let dim_pi (nm, tac_fam) : G.tac = 
    G.make @@ fun goal ->
    let+ fam = EM.push_dim_var nm @@ G.run goal tac_fam in 
    G.tp @@ S.DimPi fam

  let gen_pi =
    function
    | `Dim -> dim_pi 
    | `Tp tp -> pi tp

  let sg (tac_base : G.tac) (nm, tac_fam) : G.tac = 
    G.make @@ fun goal ->
    let+ base, fam = family tac_base (nm, tac_fam) goal in
    G.tp @@ S.Sg (base, fam)

  let id tac_tp tac_l tac_r =
    G.make @@ fun goal ->
    let* tp = G.run goal tac_tp in
    let* vtp = G.eval_tp tp in
    let+ l = tac_l vtp
    and+ r = tac_r vtp in
    G.tp @@ S.Id (tp, l, r)
end

module TypeFormationRules = FormationRules (TypeGoalTp)
module CodeFormationRules = FormationRules (TypeGoalCode)


module Univ = 
struct
  include CodeFormationRules

  let formation : tp_tac = 
    EM.ret @@ S.Tp S.Univ

  let el_formation tac = 
    let+ tm = tac @@ D.Tp D.Univ in
    S.Tp (S.El tm)
end

module Id = 
struct
  let formation = TypeFormationRules.id

  let intro : chk_tac =
    function
    | D.Tp (D.Id (tp, l, r)) ->
      let+ () = EM.equate tp l r
      and+ t = EM.lift_qu @@ Nbe.quote_con tp l in
      S.Refl t
    | tp ->
      EM.elab_err @@ Err.ExpectedConnective (`Id, tp)

  let elim (nm_x0, nm_x1, nm_p, tac_mot) (nm_x, tac_case_refl) tac_scrut : syn_tac =
    let* ghost = EM.current_ghost in
    let* tscrut, idtp = tac_scrut in
    let* tp, l, r = EM.dest_id idtp in
    let* tmot =
      EM.abstract nm_x0 tp @@ fun x0 ->
      EM.abstract nm_x1 tp @@ fun x1 ->
      EM.abstract nm_p (D.Tp (D.Id (tp, x0, x1))) @@ fun _ ->
      tac_mot
    in
    let* t_refl_case =
      EM.abstract nm_x tp @@ fun x ->
      tac_case_refl @<<
      EM.lift_ev @@ EvM.append [`Con x; `Con (D.Refl x)] @@ Nbe.eval_tp tmot
    in
    let+ fib = 
      let* vscrut = EM.lift_ev @@ Nbe.eval tscrut in
      EM.lift_ev @@ EvM.append [`Con l; `Con r; `Con vscrut] @@ Nbe.eval_tp tmot
    in
    S.IdElim (ghost, tmot, t_refl_case, tscrut), fib
end


module Pi =
struct 
  let formation = TypeFormationRules.pi 

  let intro name tac_body : chk_tac =
    function
    | D.Tp (D.Pi (base, fam)) ->
      EM.abstract name base @@ fun var ->
      let+ t = tac_body @<< EM.lift_cmp @@ Nbe.inst_tp_clo fam [var] in
      S.Lam t
    | tp ->
      EM.elab_err @@ Err.ExpectedConnective (`Pi, tp)

  let apply tac_fun tac_arg : syn_tac =
    let* tfun, tp = tac_fun in
    let* base, fam = EM.dest_pi tp in
    let* targ = tac_arg base in
    let+ fib = 
      let* varg = EM.lift_ev @@ Nbe.eval targ in
      EM.lift_cmp @@ Nbe.inst_tp_clo fam [varg] 
    in
    S.Ap (tfun, targ), fib
end

module DimPi = 
struct
  let formation = TypeFormationRules.dim_pi

  let intro name tac_body : chk_tac = 
    function
    | D.Tp (D.DimPi fam) ->
      EM.abstract_dim name @@ fun x ->
      let+ t = tac_body @<< EM.lift_cmp @@ Nbe.inst_tp_line_clo fam x in 
      S.DimLam t
    | tp ->
      EM.elab_err @@ Err.ExpectedConnective (`DimPi, tp)

  let apply tac_fun tac_arg : syn_tac = 
    let* tfun, tp = tac_fun in
    let* fam = EM.dest_dim_pi tp in
    let* tr = tac_arg in 
    let+ fib = 
      let* r = EM.lift_ev @@ Nbe.eval_dim tr in 
      EM.lift_cmp @@ Nbe.inst_tp_line_clo fam r
    in 
    S.DimAp (tfun, tr), fib
end

module Sg = 
struct
  let formation = TypeFormationRules.sg

  let intro tac_fst tac_snd : chk_tac =
    function
    | D.Tp (D.Sg (base, fam)) ->
      let* tfst = tac_fst base in
      let+ tsnd = 
        let* vfst = EM.lift_ev @@ Nbe.eval tfst in
        tac_snd @<< EM.lift_cmp @@ Nbe.inst_tp_clo fam [vfst] 
      in
      S.Pair (tfst, tsnd)
    | tp ->
      EM.elab_err @@ Err.ExpectedConnective (`Sg, tp)

  let pi1 tac : syn_tac =
    let* tpair, tp = tac in
    let+ base, _ = EM.dest_sg tp in
    S.Fst tpair, base

  let pi2 tac : syn_tac =
    let* tpair, tp = tac in
    let+ fib = 
      let* vfst = EM.lift_ev @@ Nbe.eval @@ S.Fst tpair in
      let* _, fam = EM.dest_sg tp in
      EM.lift_cmp @@ Nbe.inst_tp_clo fam [vfst] 
    in
    S.Snd tpair, fib
end


module Nat = 
struct
  let formation = TypeFormationRules.nat

  let assert_nat =
    function
    | D.Tp D.Nat -> EM.ret ()
    | tp -> EM.elab_err @@ Err.ExpectedConnective (`Nat, tp)

  let literal n : chk_tac =
    fun tp ->
    let+ () = assert_nat tp in
    int_to_term n

  let suc tac : chk_tac =
    fun tp ->
    let* () = assert_nat tp in
    let+ t = tac tp in
    S.Suc t

  let elim (nm_mot, tac_mot) tac_case_zero (nm_x, nm_ih, tac_case_suc) tac_scrut : syn_tac =
    let* ghost = EM.current_ghost in
    let* tscrut, nattp = tac_scrut in
    let* () = assert_nat nattp in

    let* tmot =
      EM.abstract nm_mot nattp @@ fun _ ->
      tac_mot
    in

    let* tcase_zero =
      tac_case_zero @<<
      EM.lift_ev @@ EvM.append [`Con D.Zero] @@ Nbe.eval_tp tmot
    in

    let* tcase_suc =
      EM.abstract nm_x nattp @@ fun x ->
      let* fib_x = EM.lift_ev @@ EvM.append [`Con x] @@ Nbe.eval_tp tmot in
      let* fib_suc_x = EM.lift_ev @@ EvM.append [`Con (D.Suc x)] @@ Nbe.eval_tp tmot in
      EM.abstract nm_ih fib_x @@ fun _ ->
      tac_case_suc fib_suc_x
    in

    let+ fib_scrut = 
      let* vscrut = EM.lift_ev @@ Nbe.eval tscrut in
      EM.lift_ev @@ EvM.append [`Con vscrut] @@ Nbe.eval_tp tmot
    in
    S.NatElim (ghost, tmot, tcase_zero, tcase_suc, tscrut), fib_scrut
end


module Structural = 
struct
  let syn_to_chk (tac : syn_tac) : chk_tac =
    fun tp ->
      let* tm, tp' = tac in
      let+ () = EM.equate_tp tp tp' in
      tm

  let chk_to_syn (tac_tm : chk_tac) (tac_tp : tp_tac) : syn_tac =
    let* tp = tac_tp in
    let* vtp = EM.lift_ev @@ Nbe.eval_tp tp in
    let+ tm = tac_tm vtp in
    tm, vtp

  let lookup_var id : syn_tac =
    let* res = EM.resolve id in
    match res with
    | `Local ix ->
      let+ tp = EM.get_local_tp ix in
      S.Var ix, tp
    | `Global sym ->
      let+ tp, _ = EM.get_global sym in
      S.Global sym, tp
    | `Unbound ->
      EM.elab_err @@ Err.UnboundVariable id

  let variable ix =
    let+ tp = EM.get_local_tp ix in 
    S.Var ix, tp

  let let_ tac_def (nm_x, tac_bdy) : chk_tac =
    fun tp ->
    let* tdef, tp_def = tac_def in
    let* vdef = EM.lift_ev @@ Nbe.eval tdef in
    EM.define nm_x tp_def vdef @@ fun _ ->
    let+ tbdy = tac_bdy tp in
    S.Let (tdef, tbdy)
end

module Tactic =
struct
  let match_goal (tac : D.tp -> chk_tac m) : chk_tac =
    fun tp ->
      let* tac = tac tp in
      tac tp

  let tac_lam name tac_body : chk_tac = 
    match_goal @@ function
    | D.Tp (D.Pi _) ->
      EM.ret @@ Pi.intro name tac_body
    | D.Tp (D.DimPi _) ->
      EM.ret @@ DimPi.intro name tac_body
    | _ ->
      EM.throw @@ Invalid_argument "tac_lam cannot be called on this goal"

  let tac_gen_pi_formation = TypeFormationRules.gen_pi

  let rec tac_multi_lam names tac_body =
    match names with
    | [] -> tac_body
    | name :: names ->
      tac_lam (Some name) @@
      tac_multi_lam names tac_body

  let rec tac_multi_apply tac_fun =
    function
    | [] -> tac_fun
    | tac :: tacs ->
      tac_multi_apply (Pi.apply tac_fun tac) tacs

  let rec tac_nary_quantifier quant cells body = 
    match cells with
    | [] -> body
    | (nm, tac) :: cells -> 
      quant tac (nm, tac_nary_quantifier quant cells body)

  module Elim =
  struct
    type case_tac = CS.pat * chk_tac

    let rec find_case (lbl : CS.ident) (cases : case_tac list) : (CS.pat_arg list * chk_tac) option = 
      match cases with 
      | (CS.Pat pat, tac) :: _ when pat.lbl = lbl ->
        Some (pat.args, tac)
      | _ :: cases ->
        find_case lbl cases
      | [] ->
        None

    let elim (mot : CS.ident option list * tp_tac) (cases : case_tac list) (scrut : syn_tac) : syn_tac =
      let* tscrut, D.Tp ind_tp = scrut in
      let scrut = EM.ret (tscrut, D.Tp ind_tp) in
      match ind_tp, mot with
      | D.Id (_, _, _), ([nm_u; nm_v; nm_p], mot) ->
        let* tac_refl =
          match find_case "refl" cases with
          | Some ([`Simple nm_w], tac) -> EM.ret (nm_w, tac)
          | Some ([], tac) -> EM.ret (None, tac)
          | Some _ -> EM.elab_err Err.MalformedCase 
          | None -> EM.ret (None, Hole.unleash_hole (Some "refl") `Rigid)
        in
        Id.elim (nm_u, nm_v, nm_p, mot) tac_refl scrut
      | D.Nat, ([nm_x], mot) ->
        let* tac_zero = 
          match find_case "zero" cases with 
          | Some ([], tac) -> EM.ret tac
          | Some _ -> EM.elab_err Err.MalformedCase
          | None -> EM.ret @@ Hole.unleash_hole (Some "zero") `Rigid
        in
        let* tac_suc =
          match find_case "suc" cases with
          | Some ([`Simple nm_z], tac) -> EM.ret (nm_z, None, tac)
          | Some ([`Inductive (nm_z, nm_ih)], tac) -> EM.ret (nm_z, nm_ih, tac)
          | Some _ -> EM.elab_err Err.MalformedCase
          | None -> EM.ret @@ (None, None, Hole.unleash_hole (Some "suc") `Rigid)
        in
        Nat.elim (nm_x, mot) tac_zero tac_suc scrut
      | _ -> 
        let* env = EM.read in
        let* tp = EM.lift_qu @@ Nbe.quote_tp (D.Tp ind_tp) in
        EM.elab_err @@ Err.CannotEliminate (Env.pp_env env, tp)

    let assert_simple_inductive =
      function
      | D.Tp D.Nat -> 
        EM.ret () 
      | tp ->
        let* env = EM.read in
        let ppenv = Env.pp_env env in
        let* tp = EM.lift_qu @@ Nbe.quote_tp tp in
        EM.elab_err @@ Err.ExpectedSimpleInductive (ppenv, tp)

    let lam_elim cases : chk_tac = 
      match_goal @@ fun tp ->
      let* base, fam = EM.dest_pi tp in
      let+ () = assert_simple_inductive base in
      let mot_tac : tp_tac =
        let* x, _ = Structural.variable 0 in
        let* vx = EM.lift_ev @@ Nbe.eval x in
        let* vmot = EM.lift_cmp @@ Nbe.inst_tp_clo fam [vx] in
        EM.lift_qu @@ Nbe.quote_tp vmot 
      in
      Pi.intro None @@
      Structural.syn_to_chk @@ 
      elim ([None], mot_tac) cases @@ 
      Structural.variable 0

  end
end