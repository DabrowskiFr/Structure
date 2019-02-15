(************************************************************************)
(* Copyright 2018 Frédéric Dabrowski                                    *)
(* 
    This program is free software:: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Foobar is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with Foobar.  If not, see <https://www.gnu.org/licenses/>.    *)
(************************************************************************)

Require Import Utf8.
Require Import Structure.Functor.

Class Monad (f : Type -> Type) `(E : Applicative f)  : Type :=
  {
    bind : ∀ {a b : Type}, f a -> (a -> f b) -> f b 
  }.

Infix ">>=" := bind (at level 28) : monad_scope.

Infix ">>" := (fun m k => bind m (fun x => k)) (at level 28) : monad_scope. 

Notation "'do' X <- A ; B" := (bind A (fun X => B))
                               (at level 200, X ident, A at level 100, B at level 200).

Instance monad_option : Monad option applicative_option :=
  {
    bind _ _ x f :=
      match x with
        Some x => f x
      | None => None
      end
  }.