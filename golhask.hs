module Golhask where

import qualified Prelude

data Bool =
   True
 | False

data Nat =
   O
 | S Nat

data List a =
   Nil
 | Cons a (List a)

beq_nat :: Nat -> Nat -> Bool
beq_nat n m =
  case n of {
   O ->
    case m of {
     O -> True;
     S m' -> False};
   S n' ->
    case m of {
     O -> False;
     S m' -> beq_nat n' m'}}

data Mark =
   Alive
 | Dead

data Cell =
   C00
 | C01
 | C02
 | C03
 | C10
 | C11
 | C12
 | C13
 | C20
 | C21
 | C22
 | C23
 | C30
 | C31
 | C32
 | C33

data Board =
   Mk_board Mark Mark Mark Mark Mark Mark Mark Mark Mark Mark Mark Mark 
 Mark Mark Mark Mark

place :: Cell -> Mark -> Board -> Board
place c m b =
  case b of {
   Mk_board b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32
    b33 ->
    case c of {
     C00 -> Mk_board m b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 b31
      b32 b33;
     C01 -> Mk_board b00 m b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 b31
      b32 b33;
     C02 -> Mk_board b00 b01 m b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 b31
      b32 b33;
     C03 -> Mk_board b00 b01 b02 m b10 b11 b12 b13 b20 b21 b22 b23 b30 b31
      b32 b33;
     C10 -> Mk_board b00 b01 b02 b03 m b11 b12 b13 b20 b21 b22 b23 b30 b31
      b32 b33;
     C11 -> Mk_board b00 b01 b02 b03 b10 m b12 b13 b20 b21 b22 b23 b30 b31
      b32 b33;
     C12 -> Mk_board b00 b01 b02 b03 b10 b11 m b13 b20 b21 b22 b23 b30 b31
      b32 b33;
     C13 -> Mk_board b00 b01 b02 b03 b10 b11 b12 m b20 b21 b22 b23 b30 b31
      b32 b33;
     C20 -> Mk_board b00 b01 b02 b03 b10 b11 b12 b13 m b21 b22 b23 b30 b31
      b32 b33;
     C21 -> Mk_board b00 b01 b02 b03 b10 b11 b12 b13 b20 m b22 b23 b30 b31
      b32 b33;
     C22 -> Mk_board b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 m b23 b30 b31
      b32 b33;
     C23 -> Mk_board b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 m b30 b31
      b32 b33;
     C30 -> Mk_board b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 m b31
      b32 b33;
     C31 -> Mk_board b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 m
      b32 b33;
     C32 -> Mk_board b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 b31
      m b33;
     C33 -> Mk_board b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 b31
      b32 m}}

initialize :: Board -> (List Cell) -> Board
initialize b l =
  case l of {
   Nil -> b;
   Cons h t -> initialize (place h Alive b) t}

get :: Board -> Cell -> Mark
get b c =
  case b of {
   Mk_board b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32
    b33 ->
    case c of {
     C00 -> b00;
     C01 -> b01;
     C02 -> b02;
     C03 -> b03;
     C10 -> b10;
     C11 -> b11;
     C12 -> b12;
     C13 -> b13;
     C20 -> b20;
     C21 -> b21;
     C22 -> b22;
     C23 -> b23;
     C30 -> b30;
     C31 -> b31;
     C32 -> b32;
     C33 -> b33}}

rec_num_nei :: Board -> (List Cell) -> Cell -> Nat
rec_num_nei b l c =
  case l of {
   Nil -> O;
   Cons h t ->
    case get b h of {
     Alive -> S (rec_num_nei b t c);
     Dead -> rec_num_nei b t c}}

apply_rules :: Board -> Board -> Cell -> Board
apply_rules b_old b_new c =
  case c of {
   C00 ->
    case beq_nat (rec_num_nei b_old (Cons C01 (Cons C10 (Cons C11 Nil))) c) O of {
     True -> b_new;
     False -> place c Alive b_new};
   C01 ->
    case beq_nat
           (rec_num_nei b_old (Cons C00 (Cons C02 (Cons C10 (Cons C11 (Cons
             C12 Nil))))) c) O of {
     True -> b_new;
     False -> place c Alive b_new};
   C02 ->
    case beq_nat
           (rec_num_nei b_old (Cons C01 (Cons C03 (Cons C11 (Cons C12 (Cons
             C13 Nil))))) c) O of {
     True -> b_new;
     False -> place c Alive b_new};
   C03 ->
    case beq_nat (rec_num_nei b_old (Cons C02 (Cons C12 (Cons C13 Nil))) c) O of {
     True -> b_new;
     False -> place c Alive b_new};
   C10 ->
    case beq_nat
           (rec_num_nei b_old (Cons C00 (Cons C01 (Cons C11 (Cons C20 (Cons
             C21 Nil))))) c) O of {
     True -> b_new;
     False -> place c Alive b_new};
   C11 ->
    case beq_nat
           (rec_num_nei b_old (Cons C00 (Cons C01 (Cons C02 (Cons C10 (Cons
             C12 (Cons C20 (Cons C21 (Cons C22 Nil)))))))) c) O of {
     True -> b_new;
     False -> place c Alive b_new};
   C12 ->
    case beq_nat
           (rec_num_nei b_old (Cons C01 (Cons C02 (Cons C03 (Cons C11 (Cons
             C13 (Cons C21 (Cons C22 (Cons C23 Nil)))))))) c) O of {
     True -> b_new;
     False -> place c Alive b_new};
   C13 ->
    case beq_nat
           (rec_num_nei b_old (Cons C02 (Cons C03 (Cons C12 (Cons C22 (Cons
             C23 Nil))))) c) O of {
     True -> b_new;
     False -> place c Alive b_new};
   C20 ->
    case beq_nat
           (rec_num_nei b_old (Cons C10 (Cons C11 (Cons C21 (Cons C30 (Cons
             C31 Nil))))) c) O of {
     True -> b_new;
     False -> place c Alive b_new};
   C21 ->
    case beq_nat
           (rec_num_nei b_old (Cons C10 (Cons C11 (Cons C12 (Cons C20 (Cons
             C22 (Cons C30 (Cons C31 (Cons C32 Nil)))))))) c) O of {
     True -> b_new;
     False -> place c Alive b_new};
   C22 ->
    case beq_nat
           (rec_num_nei b_old (Cons C11 (Cons C12 (Cons C13 (Cons C21 (Cons
             C23 (Cons C31 (Cons C32 (Cons C33 Nil)))))))) c) O of {
     True -> b_new;
     False -> place c Alive b_new};
   C23 ->
    case beq_nat
           (rec_num_nei b_old (Cons C12 (Cons C13 (Cons C22 (Cons C32 (Cons
             C33 Nil))))) c) O of {
     True -> b_new;
     False -> place c Alive b_new};
   C30 ->
    case beq_nat (rec_num_nei b_old (Cons C20 (Cons C21 (Cons C31 Nil))) c) O of {
     True -> b_new;
     False -> place c Alive b_new};
   C31 ->
    case beq_nat
           (rec_num_nei b_old (Cons C20 (Cons C21 (Cons C22 (Cons C30 (Cons
             C32 Nil))))) c) O of {
     True -> b_new;
     False -> place c Alive b_new};
   C32 ->
    case beq_nat
           (rec_num_nei b_old (Cons C21 (Cons C22 (Cons C23 (Cons C31 (Cons
             C33 Nil))))) c) O of {
     True -> b_new;
     False -> place c Alive b_new};
   C33 ->
    case beq_nat (rec_num_nei b_old (Cons C22 (Cons C23 (Cons C32 Nil))) c) O of {
     True -> b_new;
     False -> place c Alive b_new}}

update :: Board -> Board -> (List Cell) -> Board
update b_old b_new c =
  case c of {
   Nil -> b_new;
   Cons h t -> update b_old (apply_rules b_old b_new h) t}

emptyboard :: Board
emptyboard =
  Mk_board Dead Dead Dead Dead Dead Dead Dead Dead Dead Dead Dead Dead Dead
    Dead Dead Dead

all_cells :: List Cell
all_cells =
  Cons C00 (Cons C01 (Cons C02 (Cons C03 (Cons C10 (Cons C11 (Cons C12 (Cons
    C13 (Cons C20 (Cons C21 (Cons C22 (Cons C23 (Cons C30 (Cons C31 (Cons C32
    (Cons C33 Nil)))))))))))))))

do_play_game :: Board -> Nat -> Board
do_play_game b num =
  case num of {
   O -> b;
   S n -> do_play_game (update b b all_cells) n}

play_game :: (List Cell) -> Nat -> Board
play_game l n =
  do_play_game (initialize emptyboard l) n

