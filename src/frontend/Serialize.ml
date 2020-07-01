open Basis
open Core
open Cubical

module J = Ezjsonm
module S = Syntax

module type ResolveM =
sig
  include Monad.S
  val resolver : Resolver.env m
end

exception CJHM

module BasicJson (M : Monad.S) =
struct
  module MU = Monad.Util (M)
  open Monad.Notation (M)

  let json_of_int i =
    `String (string_of_int i)

  let json_of_pair (json_of_a, json_of_b) (a, b) =
    let+ ja = json_of_a a
    and+ jb = json_of_b b in
    `A [ja; jb]

  let json_of_list json_of_item l =
    let+ xs = MU.map json_of_item l in
    `A xs
end

module Serialize (M : ResolveM) =
struct
  module MU = Monad.Util (M)
  open Monad.Notation (M)
  open BasicJson (M)

  let json_of_path : Resolver.path -> J.value =
    fun path ->
    let jcells = path |> List.map @@ fun x -> `String x in
    `A jcells


  let json_of_sym : Symbol.t -> J.value m =
    fun sym ->
    let+ resolver = M.resolver in
    let paths = Resolver.unresolve sym resolver in
    json_of_path @@ Resolver.PathSet.min_elt paths

  let rec json_of_tm : S.t -> J.value m =
    function
    | Var x ->
      M.ret @@ `A [`String "Var"; json_of_int x]

    | Global sym ->
      let+ jpath = json_of_sym sym in
      `A [`String "Global"; jpath]

    | Ann (tm, tp) ->
      let+ jtm = json_of_tm tm
      and+ jtp = json_of_tp tp in
      `A [`String "Ann"; jtm; jtp]

    | Zero ->
      M.ret @@ `A [`String "Zero"]

    | Suc tm ->
      let+ jtm = json_of_tm tm in
      `A [`String "Suc"; jtm]

    | NatElim (tm0, tm1, tm2, tm3) ->
      let+ jtm0 = json_of_tm tm0
      and+ jtm1 = json_of_tm tm1
      and+ jtm2 = json_of_tm tm2
      and+ jtm3 = json_of_tm tm3 in
      `A [`String "NatElim"; jtm0; jtm1; jtm2; jtm3]

    | Base ->
      M.ret @@ `A [`String "Base"]

    | Loop tm ->
      let+ jtm = json_of_tm tm in
      `A [`String "Loop"; jtm]

    | CircleElim (tm0, tm1, tm2, tm3) ->
      let+ jtm0 = json_of_tm tm0
      and+ jtm1 = json_of_tm tm1
      and+ jtm2 = json_of_tm tm2
      and+ jtm3 = json_of_tm tm3 in
      `A [`String "CircleElim"; jtm0; jtm1; jtm2; jtm3]

    | Lam (_, tm) ->
      let+ jtm = json_of_tm tm in
      `A [`String "Lam"; jtm]

    | Ap (tm0, tm1) ->
      let+ jtm0 = json_of_tm tm0
      and+ jtm1 = json_of_tm tm1 in
      `A [`String "Ap"; jtm0; jtm1]

    | Pair (tm0, tm1) ->
      let+ jtm0 = json_of_tm tm0
      and+ jtm1 = json_of_tm tm1 in
      `A [`String "Pair"; jtm0; jtm1]

    | Fst tm ->
      let+ jtm = json_of_tm tm in
      `A [`String "Fst"; jtm]

    | Snd tm ->
      let+ jtm = json_of_tm tm in
      `A [`String "Snd"; jtm]

    | GoalRet tm ->
      let+ jtm = json_of_tm tm in
      `A [`String "GoalRet"; jtm]

    | GoalProj tm ->
      let+ jtm = json_of_tm tm in
      `A [`String "GoalProj"; jtm]

    | Coe (tm0, tm1, tm2, tm3) ->
      let+ jtm0 = json_of_tm tm0
      and+ jtm1 = json_of_tm tm1
      and+ jtm2 = json_of_tm tm2
      and+ jtm3 = json_of_tm tm3 in
      `A [`String "Coe"; jtm0; jtm1; jtm2; jtm3]

    | Com (tm0, tm1, tm2, tm3, tm4) ->
      let+ jtm0 = json_of_tm tm0
      and+ jtm1 = json_of_tm tm1
      and+ jtm2 = json_of_tm tm2
      and+ jtm3 = json_of_tm tm3
      and+ jtm4 = json_of_tm tm4 in
      `A [`String "Com"; jtm0; jtm1; jtm2; jtm3; jtm4]

    | HCom (tm0, tm1, tm2, tm3, tm4) ->
      let+ jtm0 = json_of_tm tm0
      and+ jtm1 = json_of_tm tm1
      and+ jtm2 = json_of_tm tm2
      and+ jtm3 = json_of_tm tm3
      and+ jtm4 = json_of_tm tm4 in
      `A [`String "HCom"; jtm0; jtm1; jtm2; jtm3; jtm4]

    | SubIn tm ->
      let+ jtm = json_of_tm tm in
      `A [`String "SubIn"; jtm]

    | SubOut tm ->
      let+ jtm = json_of_tm tm in
      `A [`String "SubOut"; jtm]

    | ElIn tm ->
      let+ jtm = json_of_tm tm in
      `A [`String "ElIn"; jtm]

    | ElOut tm ->
      let+ jtm = json_of_tm tm in
      `A [`String "ElOut"; jtm]

    | Dim0 ->
      M.ret @@ `A [`String "Dim0"]

    | Dim1 ->
      M.ret @@ `A [`String "Dim1"]

    | Prf ->
      M.ret @@ `A [`String "Prf"]

    | Cof cof ->
      let+ jcof = json_of_cof_f cof in
      `A [`String "Cof"; jcof]

    | ForallCof tm ->
      let+ jtm = json_of_tm tm in
      `A [`String "ForallCof"; jtm]

    | CofSplit branches ->
      let+ jbranches = json_of_list (json_of_pair (json_of_tm, json_of_tm)) branches in
      `A [`String "CofSplit"; jbranches]

    | Box (tm0, tm1, tm2, tm3, tm4) ->
      let+ jtm0 = json_of_tm tm0
      and+ jtm1 = json_of_tm tm1
      and+ jtm2 = json_of_tm tm2
      and+ jtm3 = json_of_tm tm3
      and+ jtm4 = json_of_tm tm4 in
      `A [`String "Box"; jtm0; jtm1; jtm2; jtm3; jtm4]

    | Cap (tm0, tm1, tm2, tm3, tm4) ->
      let+ jtm0 = json_of_tm tm0
      and+ jtm1 = json_of_tm tm1
      and+ jtm2 = json_of_tm tm2
      and+ jtm3 = json_of_tm tm3
      and+ jtm4 = json_of_tm tm4 in
      `A [`String "Cap"; jtm0; jtm1; jtm2; jtm3; jtm4]

    | VIn (tm0, tm1, tm2, tm3) ->
      let+ jtm0 = json_of_tm tm0
      and+ jtm1 = json_of_tm tm1
      and+ jtm2 = json_of_tm tm2
      and+ jtm3 = json_of_tm tm3 in
      `A [`String "VIn"; jtm0; jtm1; jtm2; jtm3]

    | VProj (tm0, tm1, tm2, tm3, tm4) ->
      let+ jtm0 = json_of_tm tm0
      and+ jtm1 = json_of_tm tm1
      and+ jtm2 = json_of_tm tm2
      and+ jtm3 = json_of_tm tm3
      and+ jtm4 = json_of_tm tm4 in
      `A [`String "VProj"; jtm0; jtm1; jtm2; jtm3; jtm4]


    | CodeExt (i, tm0, `Global tm1, tm2) ->
      let+ jtm0 = json_of_tm tm0
      and+ jtm1 = json_of_tm tm1
      and+ jtm2 = json_of_tm tm2 in
      `A [`String "CodeExt"; json_of_int i; jtm0; jtm1; jtm2]

    | CodePi (tm0, tm1) ->
      let+ jtm0 = json_of_tm tm0
      and+ jtm1 = json_of_tm tm1 in
      `A [`String "CodePi"; jtm0; jtm1]

    | CodeSg (tm0, tm1) ->
      let+ jtm0 = json_of_tm tm0
      and+ jtm1 = json_of_tm tm1 in
      `A [`String "CodeSg"; jtm0; jtm1]

    | CodeV (tm0, tm1, tm2, tm3) ->
      let+ jtm0 = json_of_tm tm0
      and+ jtm1 = json_of_tm tm1
      and+ jtm2 = json_of_tm tm2
      and+ jtm3 = json_of_tm tm3 in
      `A [`String "CodeV"; jtm0; jtm1; jtm2; jtm3]

    | CodeCircle ->
      M.ret @@ `A [`String "CodeCircle"]

    | CodeNat ->
      M.ret @@ `A [`String "CodeNat"]

    | CodeUniv ->
      M.ret @@ `A [`String "CodeUniv"]

    | ESub (sub, tm) ->
      let+ jsub = json_of_sub sub
      and+ jtm = json_of_tm tm in
      `A [`String "ESub"; jsub; jtm]

    | Let (tm0, _, tm1) ->
      let+ jtm0 = json_of_tm tm0
      and+ jtm1 = json_of_tm tm1 in
      `A [`String "Let"; jtm0; jtm1]


  and json_of_sub : S.sub -> J.value m =
    function
    | Sb1 ->
      M.ret @@ `A [`String "Sb1"]
    | SbI ->
      M.ret @@ `A [`String "SbI"]
    | SbP ->
      M.ret @@ `A [`String "SbP"]
    | SbE (sub, tm) ->
      let+ jsub = json_of_sub sub
      and+ jtm = json_of_tm tm in
      `A [`String "SbE"; jsub; jtm]
    | SbC (sub0, sub1) ->
      let+ jsub0 = json_of_sub sub0
      and+ jsub1 = json_of_sub sub1 in
      `A [`String "SbC"; jsub0; jsub1]

  and json_of_cof_f : (S.t, S.t) Cof.cof_f -> J.value m =
    function
    | Cof.Eq (r0, r1) ->
      let+ jr0 = json_of_tm r0
      and+ jr1 = json_of_tm r1 in
      `A [`String "Eq"; jr0; jr1]

    | Cof.Join cofs ->
      let+ jcofs = MU.map json_of_tm cofs in
      `A [`String "Join"; `A jcofs]

    | Cof.Meet cofs ->
      let+ jcofs = MU.map json_of_tm cofs in
      `A [`String "Meet"; `A jcofs]

  and json_of_tp : S.tp -> J.value m =
    function
    | _ -> raise CJHM

end
