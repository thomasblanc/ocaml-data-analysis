open Common_types

module TIdm : Utils.Map.S with type key = TId.t

type atpl

val of_tid : TId.t -> atpl
val print_atpl : Format.formatter -> atpl -> unit

module Locs : Utils.Set.S with type elt = atpl
module Locm : sig
  include Utils.Map.S with type key = atpl
  val fold_key : ( key -> 'a -> 'b -> 'b) -> key -> 'a t -> 'b -> 'b
  val fold_by_loc : (key -> 'b -> 'b) -> 'a t -> 'b -> 'b
end
