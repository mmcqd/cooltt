open Core
open CodeUnit
module CS := ConcreteSyntax
module S := Syntax
module RM := Monads.RefineM
module D := Domain

open Tactic

val chk_tp : CS.con -> Tp.tac
val chk_tp_in_tele : CS.cell list -> CS.con -> Tp.tac
val chk_tm : CS.con -> Chk.tac
val chk_tm_in_tele : CS.cell list -> CS.con -> Chk.tac
val syn_tm : CS.con -> Syn.tac
val modifier : CS.con option -> [> `Print of string option] Yuujinchou.Pattern.t RM.m

val elaborate_typed_term : string -> CS.cell list -> CS.con -> CS.con -> (D.tp * D.con) RM.m
