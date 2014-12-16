(* Game Of Life
  Ty Dang, Li-Chang Wang, Sung-Min Park
*)


Extraction Language Haskell.


(* Some definitions and notations that help *)
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Notation "x :: l" := (cons x l) (at level 60, right associativity).

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Definition blt_nat (n m : nat) : bool :=

  match beq_nat n m with
    | true => false
    | false => ble_nat n m
  end.


(* A mark on the board where each cell can be dead or alive *)
Inductive mark : Set :=
  | alive : mark
  | dead : mark.

(* A cell represented on a 4x4 grid *)
Inductive cell : Set := 
  | C00: cell
  | C01: cell
  | C02: cell
  | C03: cell
  | C10: cell
  | C11: cell
  | C12: cell
  | C13: cell
  | C20: cell
  | C21: cell
  | C22: cell
  | C23: cell
  | C30: cell
  | C31: cell
  | C32: cell
  | C33: cell.

(* A board of size 4x4 made of marks *)
Inductive board := 
  mk_board: mark -> mark -> mark -> mark -> 
            mark -> mark -> mark -> mark -> 
            mark -> mark -> mark -> mark -> 
            mark -> mark -> mark -> mark -> board.

(* Place a mark at the cell location for the given board and returns a new board *)
Definition place (c: cell) (m : mark) (b : board) : board :=
  match b with
  | mk_board b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 b33 => 
      match c with
      | C00 => mk_board m b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 b33
      | C01 => mk_board b00 m b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 b33
      | C02 => mk_board b00 b01 m b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 b33
      | C03 => mk_board b00 b01 b02 m b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 b33
      | C10 => mk_board b00 b01 b02 b03 m b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 b33
      | C11 => mk_board b00 b01 b02 b03 b10 m b12 b13 b20 b21 b22 b23 b30 b31 b32 b33
      | C12 => mk_board b00 b01 b02 b03 b10 b11 m b13 b20 b21 b22 b23 b30 b31 b32 b33
      | C13 => mk_board b00 b01 b02 b03 b10 b11 b12 m b20 b21 b22 b23 b30 b31 b32 b33
      | C20 => mk_board b00 b01 b02 b03 b10 b11 b12 b13 m b21 b22 b23 b30 b31 b32 b33
      | C21 => mk_board b00 b01 b02 b03 b10 b11 b12 b13 b20 m b22 b23 b30 b31 b32 b33
      | C22 => mk_board b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 m b23 b30 b31 b32 b33
      | C23 => mk_board b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 m b30 b31 b32 b33
      | C30 => mk_board b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 m b31 b32 b33
      | C31 => mk_board b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 m b32 b33
      | C32 => mk_board b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 m b33
      | C33 => mk_board b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 m
      end
  end.

(* Initialize the board given a list of cells to mark as alive *)
Fixpoint initialize (b : board) (l : list cell) : board :=
  match l with
  | nil => b
  | cons h t => initialize (place h alive b) t
  end.

(* Get the mark value at the cell location on the given board *)
Definition get (b: board) (c: cell) : mark :=
  match b with
  | mk_board b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 b33 => 
      match c with
      | C00 => b00
      | C01 => b01
      | C02 => b02
      | C03 => b03
      | C10 => b10
      | C11 => b11
      | C12 => b12
      | C13 => b13
      | C20 => b20
      | C21 => b21
      | C22 => b22
      | C23 => b23
      | C30 => b30
      | C31 => b31
      | C32 => b32
      | C33 => b33
      end
  end.

(* Return the number of alive neighbors around the given cell. The neighbors list is passed into the function *)
Fixpoint rec_num_nei (b:board) (l: list cell) (c: cell) : nat :=
  match l with
  | nil => 0
  | h :: t => match (get b h) with
              | alive => S (rec_num_nei b t c)
              | dead => (rec_num_nei b t c)
              end
  end.

(* Apply the Game of Life rules on the given cell and return the new board *)
Definition apply_rules (b_old: board) (b_new: board) (c: cell) : board :=
  match b_old with
  | mk_board b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 b33 => 
      match c with
      | C00 => if( beq_nat (rec_num_nei b_old [C01; C10; C11] c) 0) then b_new else (place c alive b_new)
      | C01 => if( beq_nat (rec_num_nei b_old [C00; C02; C10; C11; C12] c) 0) then b_new else (place c alive b_new)
      | C02 => if( beq_nat (rec_num_nei b_old [C01; C03; C11; C12; C13] c) 0) then b_new else (place c alive b_new)
      | C03 => if( beq_nat (rec_num_nei b_old [C02; C12; C13] c) 0) then b_new else (place c alive b_new)
      | C10 => if( beq_nat (rec_num_nei b_old [C00; C01; C11; C20; C21] c) 0) then b_new else (place c alive b_new)
      | C11 => if( beq_nat (rec_num_nei b_old [C00; C01; C02; C10; C12; C20; C21; C22] c) 0) then b_new else (place c alive b_new)
      | C12 => if( beq_nat (rec_num_nei b_old [C01; C02; C03; C11; C13; C21; C22; C23] c) 0) then b_new else (place c alive b_new)
      | C13 => if( beq_nat (rec_num_nei b_old [C02; C03; C12; C22; C23] c) 0) then b_new else (place c alive b_new)
      | C20 => if( beq_nat (rec_num_nei b_old [C10; C11; C21; C30; C31] c) 0) then b_new else (place c alive b_new)
      | C21 => if( beq_nat (rec_num_nei b_old [C10; C11; C12; C20; C22; C30; C31; C32] c) 0) then b_new else (place c alive b_new)
      | C22 => if( beq_nat (rec_num_nei b_old [C11; C12; C13; C21; C23; C31; C32; C33] c) 0) then b_new else (place c alive b_new)
      | C23 => if( beq_nat (rec_num_nei b_old [C12; C13; C22; C32; C33] c) 0) then b_new else (place c alive b_new)
      | C30 => if( beq_nat (rec_num_nei b_old [C20; C21; C31]  c) 0) then b_new else (place c alive b_new)
      | C31 => if( beq_nat (rec_num_nei b_old [C20; C21; C22; C30; C32] c) 0) then b_new else (place c alive b_new)
      | C32 => if( beq_nat (rec_num_nei b_old [C21; C22; C23; C31; C33] c) 0) then b_new else (place c alive b_new)
      | C33 => if( beq_nat (rec_num_nei b_old [C22; C23; C32] c) 0) then b_new else (place c alive b_new)
      end
  end.

(* This would not compile... too big?
Definition apply_rules (b_old: board) (b_new: board) (c: cell) : board :=
  match c, get b_old c with
    | C00, alive => if( blt_nat (rec_num_nei b_old [C01; C10; C11] c) 2) then (place c dead b_new) else
                    if( beq_nat (rec_num_nei b_old [C01; C10; C11] c) 2) then b_new else
                    if( beq_nat (rec_num_nei b_old [C01; C10; C11] c) 3) then b_new else
                    if( blt_nat (rec_num_nei b_old [C01; C10; C11] c) 4) then b_new else (place c dead b_new)
    | C00, dead => if( beq_nat (rec_num_nei b_old [C01; C10; C11] c) 3) then (place c alive b_new) else b_new
    | C01, alive => if( blt_nat (rec_num_nei b_old [C00; C02; C10; C11; C12] c) 2) then (place c dead b_new) else
                    if( beq_nat (rec_num_nei b_old [C00; C02; C10; C11; C12] c) 2) then b_new else
                    if( beq_nat (rec_num_nei b_old [C00; C02; C10; C11; C12] c) 3) then b_new else
                    if( blt_nat (rec_num_nei b_old [C00; C02; C10; C11; C12] c) 4) then b_new else (place c dead b_new)
    | C01, dead => if( beq_nat (rec_num_nei b_old [C00; C02; C10; C11; C12] c) 3) then (place c alive b_new) else b_new
    | C02, alive => if( blt_nat (rec_num_nei b_old [C01; C03; C11; C12; C13] c) 2) then (place c dead b_new) else
                    if( beq_nat (rec_num_nei b_old [C01; C03; C11; C12; C13] c) 2) then b_new else
                    if( beq_nat (rec_num_nei b_old [C01; C03; C11; C12; C13] c) 3) then b_new else
                    if( blt_nat (rec_num_nei b_old [C01; C03; C11; C12; C13] c) 4) then b_new else (place c dead b_new)
    | C02, dead => if( beq_nat (rec_num_nei b_old [C01; C03; C11; C12; C13] c) 3) then (place c alive b_new) else b_new
    | C03, alive => if( blt_nat (rec_num_nei b_old [C02; C12; C13] c) 2) then (place c dead b_new) else
                    if( beq_nat (rec_num_nei b_old [C02; C12; C13] c) 2) then b_new else
                    if( beq_nat (rec_num_nei b_old [C02; C12; C13] c) 3) then b_new else
                    if( blt_nat (rec_num_nei b_old [C02; C12; C13] c) 4) then b_new else (place c dead b_new)
    | C03, dead => if( beq_nat (rec_num_nei b_old [C02; C12; C13] c) 3) then (place c alive b_new) else b_new
    | C10, alive => if( blt_nat (rec_num_nei b_old [C00; C01; C11; C20; C21] c) 2) then (place c dead b_new) else
                    if( beq_nat (rec_num_nei b_old [C00; C01; C11; C20; C21] c) 2) then b_new else
                    if( beq_nat (rec_num_nei b_old [C00; C01; C11; C20; C21] c) 3) then b_new else
                    if( blt_nat (rec_num_nei b_old [C00; C01; C11; C20; C21] c) 4) then b_new else (place c dead b_new)
    | C10, dead => if( beq_nat (rec_num_nei b_old [C00; C01; C11; C20; C21] c) 3) then (place c alive b_new) else b_new
    | C11, alive => if( blt_nat (rec_num_nei b_old [C00; C01; C02; C10; C12; C20; C21; C22] c) 2) then (place c dead b_new) else
                    if( beq_nat (rec_num_nei b_old [C00; C01; C02; C10; C12; C20; C21; C22] c) 2) then b_new else
                    if( beq_nat (rec_num_nei b_old [C00; C01; C02; C10; C12; C20; C21; C22] c) 3) then b_new else
                    if( blt_nat (rec_num_nei b_old [C00; C01; C02; C10; C12; C20; C21; C22] c) 4) then b_new else (place c dead b_new)
    | C11, dead => if( beq_nat (rec_num_nei b_old [C00; C01; C02; C10; C12; C20; C21; C22] c) 3) then (place c alive b_new) else b_new
    | C12, alive => if( blt_nat (rec_num_nei b_old [C01; C02; C03; C11; C13; C21; C22; C23] c) 2) then (place c dead b_new) else
                    if( beq_nat (rec_num_nei b_old [C01; C02; C03; C11; C13; C21; C22; C23] c) 2) then b_new else
                    if( beq_nat (rec_num_nei b_old [C01; C02; C03; C11; C13; C21; C22; C23] c) 3) then b_new else
                    if( blt_nat (rec_num_nei b_old [C01; C02; C03; C11; C13; C21; C22; C23] c) 4) then b_new else (place c dead b_new)
    | C12, dead => if( beq_nat (rec_num_nei b_old [C01; C02; C03; C11; C13; C21; C22; C23] c) 3) then (place c alive b_new) else b_new
    | C13, alive => if( blt_nat (rec_num_nei b_old [C02; C03; C12; C22; C23] c) 2) then (place c dead b_new) else
                    if( beq_nat (rec_num_nei b_old [C02; C03; C12; C22; C23] c) 2) then b_new else
                    if( beq_nat (rec_num_nei b_old [C02; C03; C12; C22; C23] c) 3) then b_new else
                    if( blt_nat (rec_num_nei b_old [C02; C03; C12; C22; C23] c) 4) then b_new else (place c dead b_new)
    | C13, dead => if( beq_nat (rec_num_nei b_old [C02; C03; C12; C22; C23] c) 3) then (place c alive b_new) else b_new
    | C20, alive => if( blt_nat (rec_num_nei b_old [C10; C11; C21; C30; C31] c) 2) then (place c dead b_new) else
                    if( beq_nat (rec_num_nei b_old [C10; C11; C21; C30; C31] c) 2) then b_new else
                    if( beq_nat (rec_num_nei b_old [C10; C11; C21; C30; C31] c) 3) then b_new else
                    if( blt_nat (rec_num_nei b_old [C10; C11; C21; C30; C31] c) 4) then b_new else (place c dead b_new)
    | C20, dead => if( beq_nat (rec_num_nei b_old [C10; C11; C21; C30; C31] c) 3) then (place c alive b_new) else b_new
    | C21, alive => if( blt_nat (rec_num_nei b_old [C10; C11; C12; C20; C22; C30; C31; C32] c) 2) then (place c dead b_new) else
                    if( beq_nat (rec_num_nei b_old [C10; C11; C12; C20; C22; C30; C31; C32] c) 2) then b_new else
                    if( beq_nat (rec_num_nei b_old [C10; C11; C12; C20; C22; C30; C31; C32] c) 3) then b_new else
                    if( blt_nat (rec_num_nei b_old [C10; C11; C12; C20; C22; C30; C31; C32] c) 4) then b_new else (place c dead b_new)
    | C21, dead => if( beq_nat (rec_num_nei b_old [C10; C11; C12; C20; C22; C30; C31; C32] c) 3) then (place c alive b_new) else b_new
    | C22, alive => if( blt_nat (rec_num_nei b_old [C11; C12; C13; C21; C23; C31; C32; C33] c) 2) then (place c dead b_new) else
                    if( beq_nat (rec_num_nei b_old [C11; C12; C13; C21; C23; C31; C32; C33] c) 2) then b_new else
                    if( beq_nat (rec_num_nei b_old [C11; C12; C13; C21; C23; C31; C32; C33] c) 3) then b_new else
                    if( blt_nat (rec_num_nei b_old [C11; C12; C13; C21; C23; C31; C32; C33] c) 4) then b_new else (place c dead b_new)
    | C22, dead => if( beq_nat (rec_num_nei b_old [C11; C12; C13; C21; C23; C31; C32; C33] c) 3) then (place c alive b_new) else b_new
    | C23, alive => if( blt_nat (rec_num_nei b_old [C12; C13; C22; C32; C33] c) 2) then (place c dead b_new) else
                    if( beq_nat (rec_num_nei b_old [C12; C13; C22; C32; C33] c) 2) then b_new else
                    if( beq_nat (rec_num_nei b_old [C12; C13; C22; C32; C33] c) 3) then b_new else
                    if( blt_nat (rec_num_nei b_old [C12; C13; C22; C32; C33] c) 4) then b_new else (place c dead b_new)
    | C23, dead => if( beq_nat (rec_num_nei b_old [C12; C13; C22; C32; C33] c) 3) then (place c alive b_new) else b_new
    | C30, alive => if( blt_nat (rec_num_nei b_old [C20; C21; C31] c) 2) then (place c dead b_new) else
                    if( beq_nat (rec_num_nei b_old [C20; C21; C31] c) 2) then b_new else
                    if( beq_nat (rec_num_nei b_old [C20; C21; C31] c) 3) then b_new else
                    if( blt_nat (rec_num_nei b_old [C20; C21; C31] c) 4) then b_new else (place c dead b_new)
    | C30, dead => if( beq_nat (rec_num_nei b_old [C20; C21; C31] c) 3) then (place c alive b_new) else b_new
    | C31, alive => if( blt_nat (rec_num_nei b_old [C20; C21; C22; C30; C32] c) 2) then (place c dead b_new) else
                    if( beq_nat (rec_num_nei b_old [C20; C21; C22; C30; C32] c) 2) then b_new else
                    if( beq_nat (rec_num_nei b_old [C20; C21; C22; C30; C32] c) 3) then b_new else
                    if( blt_nat (rec_num_nei b_old [C20; C21; C22; C30; C32] c) 4) then b_new else (place c dead b_new)
    | C31, dead => if( beq_nat (rec_num_nei b_old [C20; C21; C22; C30; C32] c) 3) then (place c alive b_new) else b_new
    | C32, alive => if( blt_nat (rec_num_nei b_old [C21; C22; C23; C31; C33] c) 2) then (place c dead b_new) else
                    if( beq_nat (rec_num_nei b_old [C21; C22; C23; C31; C33] c) 2) then b_new else
                    if( beq_nat (rec_num_nei b_old [C21; C22; C23; C31; C33] c) 3) then b_new else
                    if( blt_nat (rec_num_nei b_old [C21; C22; C23; C31; C33] c) 4) then b_new else (place c dead b_new)
    | C32, dead => if( beq_nat (rec_num_nei b_old [C21; C22; C23; C31; C33] c) 3) then (place c alive b_new) else b_new
    | C33, alive => if( blt_nat (rec_num_nei b_old [C22; C23; C32] c) 2) then (place c dead b_new) else
                    if( beq_nat (rec_num_nei b_old [C22; C23; C32] c) 2) then b_new else
                    if( beq_nat (rec_num_nei b_old [C22; C23; C32] c) 3) then b_new else
                    if( blt_nat (rec_num_nei b_old [C22; C23; C32] c) 4) then b_new else (place c dead b_new)
    | C33, dead => if( beq_nat (rec_num_nei b_old [C22; C23; C32] c) 3) then (place c alive b_new) else b_new
  end.
*)

(* Update the board by applying the game of life rules on each cell *)
Fixpoint update (b_old: board)(b_new: board)(c: list cell): board :=
  match c with
  | nil => b_new
  | h :: t => update b_old (apply_rules b_old b_new h) t
  end.

Definition emptyboard := mk_board dead dead dead dead 
                           dead dead dead dead
                           dead dead dead dead
                           dead dead dead dead.
Definition fullboard := mk_board alive alive alive alive
                                 alive alive alive alive
                                 alive alive alive alive
                                 alive alive alive alive.
Definition all_cells := [C00; C01; C02; C03; C10; C11; C12; C13; C20; C21; C22; C23; C30; C31; C32; C33].
Definition board1 := mk_board dead alive dead dead
                              dead dead dead dead
                              dead dead dead dead
                              dead dead dead dead.
Definition board2 := mk_board alive alive alive dead
                              alive alive alive dead
                              dead dead dead dead
                              dead dead dead dead.
Definition board3 := mk_board alive alive alive alive
                              alive alive alive alive
                              alive alive alive alive
                              dead dead dead dead.

(* Play the game for "num" iterations *)
Fixpoint do_play_game (b: board) (num: nat) : board :=
  match num with
  | O => b
  | S n => do_play_game (update b b all_cells) n
  end.

(* Start the game passing in a list of alive cells and a number of iterations *)
Definition play_game (l: list cell) (n: nat) : board :=
  do_play_game (initialize emptyboard l) n.

Compute play_game [C01;C10;C11] 0.


(* Some proofs *)
Theorem emptyboard_no_nei_c00 : rec_num_nei emptyboard [C01; C10; C11] C00 = 0.
Proof.
simpl.
reflexivity.
Qed.

Theorem emptyboard_no_change_c00 : apply_rules emptyboard emptyboard C00 = emptyboard.
Proof.
simpl.
reflexivity.
Qed.

Theorem emptyboard_no_change_all : forall c:cell, apply_rules emptyboard emptyboard c = emptyboard.
Proof.
simpl.
destruct c.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
Qed.

Theorem emptyboard_no_change_all_do_play_game : forall n:nat, do_play_game emptyboard n = emptyboard.
Proof.
simpl.
induction n.
simpl.
reflexivity.
simpl.
apply IHn.
Qed.

Theorem fullboard_is_fullboard : forall n:nat, do_play_game fullboard n = fullboard.
Proof.
simpl.
induction n.
simpl.
reflexivity.
simpl.
apply IHn.
Qed.

(* Note, these last few theorems are in relation to board1 to prove "fullboard-ness" *)
Theorem board3_onestep_full : do_play_game board3 1 = fullboard.
Proof.
simpl.
reflexivity.
Qed.

Theorem board2_twostep_full : do_play_game board2 2 = fullboard.
Proof.
simpl.
reflexivity.
Qed.

Theorem board1_threestep_full : do_play_game board1 3 = fullboard.
Proof.
simpl.
reflexivity.
Qed.

Theorem full_by_3_board1 : forall (n:nat), n > 2 -> do_play_game board1 n = fullboard.
Proof.
intros.
induction n.
inversion H.
induction n.
inversion H.
inversion H1.
induction n.
inversion H.
inversion H1.
inversion H3.
induction n.
apply board1_threestep_full.
apply fullboard_is_fullboard.
Qed.

(* These were other attempts at doing a "full by 3" proof *)
Theorem full_by_3_board1' : forall (n:nat), n > 2 -> do_play_game board1 n = 
  mk_board alive alive alive alive
           alive alive alive alive
           alive alive alive alive
           alive alive alive alive.
Proof.
intros.
induction n.
inversion H.
simpl.
induction n.
simpl.
rewrite <- IHn.
inversion H.
inversion H1.
inversion H.
inversion H1.
simpl.
rewrite <- IHn0.
inversion H.
simpl.
rewrite <- IHn0.
simpl.
rewrite <- H1.
simpl.
reflexivity.
Abort.

Theorem full_by_3' : forall (n:nat) (lc: list cell), n > 2 -> length lc > 0 -> play_game lc n = 
  mk_board alive alive alive alive
           alive alive alive alive
           alive alive alive alive
           alive alive alive alive.
Proof.
intros.
induction n.
inversion H.
Abort.


(* Extract to Haskell *)
Extraction "golhask" play_game.
Extract Inductive mark => "mark" [ "alive" "dead" ].
Extract Inductive cell => "cell" [ "C00" "C01" "C02" "C03"
                                   "C10" "C11" "C12" "C13"
                                   "C20" "C21" "C22" "C23"
                                   "C30" "C31" "C32" "C33" ].
Extract Inductive board => "board" [ "mark -> mark -> mark -> mark -> 
                                      mark -> mark -> mark -> mark -> 
                                      mark -> mark -> mark -> mark -> 
                                      mark -> mark -> mark -> mark" ].


(* Some testing *)

Compute place C00 alive emptyboard.
Compute place C23 alive emptyboard.

Example mylist := cons C00 (cons C01(cons C02 nil)).
Compute initialize emptyboard mylist.

Definition list10 := [C00].
Compute initialize emptyboard list10.

Compute update (initialize emptyboard list10) (initialize emptyboard list10)  all_cells.

Definition list_fancy := [C00; C01; C02; C10; C12; C20; C21; C22].
Example test_list_fancy : rec_num_nei emptyboard list_fancy C11 = 0.
Proof. reflexivity. Qed.

Definition b10 := mk_board alive alive alive dead alive alive alive dead alive alive alive dead dead dead dead dead.
Example test_b10 : rec_num_nei b10 list_fancy C11 = 8.
Proof. reflexivity. Qed.


(* An attempt at making the game CoInductive with an infinite while loop *)
(*
CoInductive board' := 
  mk_board': mark -> mark -> mark -> mark -> 
            mark -> mark -> mark -> mark -> 
            mark -> mark -> mark -> mark -> 
            mark -> mark -> mark -> mark -> board'.

Definition place' (c: cell) (m : mark) (b : board') : board' :=
  match b with
  | mk_board' b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 b33 => 
      match c with
      | C00 => mk_board' m b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 b33
      | C01 => mk_board' b00 m b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 b33
      | C02 => mk_board' b00 b01 m b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 b33
      | C03 => mk_board' b00 b01 b02 m b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 b33
      | C10 => mk_board' b00 b01 b02 b03 m b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 b33
      | C11 => mk_board' b00 b01 b02 b03 b10 m b12 b13 b20 b21 b22 b23 b30 b31 b32 b33
      | C12 => mk_board' b00 b01 b02 b03 b10 b11 m b13 b20 b21 b22 b23 b30 b31 b32 b33
      | C13 => mk_board' b00 b01 b02 b03 b10 b11 b12 m b20 b21 b22 b23 b30 b31 b32 b33
      | C20 => mk_board' b00 b01 b02 b03 b10 b11 b12 b13 m b21 b22 b23 b30 b31 b32 b33
      | C21 => mk_board' b00 b01 b02 b03 b10 b11 b12 b13 b20 m b22 b23 b30 b31 b32 b33
      | C22 => mk_board' b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 m b23 b30 b31 b32 b33
      | C23 => mk_board' b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 m b30 b31 b32 b33
      | C30 => mk_board' b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 m b31 b32 b33
      | C31 => mk_board' b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 m b32 b33
      | C32 => mk_board' b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 m b33
      | C33 => mk_board' b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 m
      end
  end.

Definition get' (b: board') (c: cell) : mark :=
  match b with
  | mk_board' b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 b33 => 
      match c with
      | C00 => b00
      | C01 => b01
      | C02 => b02
      | C03 => b03
      | C10 => b10
      | C11 => b11
      | C12 => b12
      | C13 => b13
      | C20 => b20
      | C21 => b21
      | C22 => b22
      | C23 => b23
      | C30 => b30
      | C31 => b31
      | C32 => b32
      | C33 => b33
      end
  end.


Fixpoint rec_num_nei' (b:board') (l: list cell) (c: cell) : nat :=
  match l with
  | nil => 0
  | h :: t => match (get' b h) with
              | alive => S (rec_num_nei' b t c)
              | dead => (rec_num_nei' b t c)
              end
  end.

Definition apply_rules' (b_old: board') (b_new: board') (c: cell) : board' :=
  match b_old with
  | mk_board' b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 b33 => 
      match c with
      | C00 => if( beq_nat (rec_num_nei' b_old [C01; C10; C11] c) 0) then b_new else (place' c alive b_new)
      | C01 => if( beq_nat (rec_num_nei' b_old [C00; C02; C10; C11; C12] c) 0) then b_new else (place' c alive b_new)
      | C02 => if( beq_nat (rec_num_nei' b_old [C01; C03; C11; C12; C13] c) 0) then b_new else (place' c alive b_new)
      | C03 => if( beq_nat (rec_num_nei' b_old [C02; C12; C13] c) 0) then b_new else (place' c alive b_new)
      | C10 => if( beq_nat (rec_num_nei' b_old [C00; C01; C11; C20; C21] c) 0) then b_new else (place' c alive b_new)
      | C11 => if( beq_nat (rec_num_nei' b_old [C00; C01; C02; C10; C12; C20; C21; C22] c) 0) then b_new else (place' c alive b_new)
      | C12 => if( beq_nat (rec_num_nei' b_old [C01; C02; C03; C11; C13; C21; C22; C23] c) 0) then b_new else (place' c alive b_new)
      | C13 => if( beq_nat (rec_num_nei' b_old [C02; C03; C12; C22; C23] c) 0) then b_new else (place' c alive b_new)
      | C20 => if( beq_nat (rec_num_nei' b_old [C10; C11; C21; C30; C31] c) 0) then b_new else (place' c alive b_new)
      | C21 => if( beq_nat (rec_num_nei' b_old [C10; C11; C12; C20; C22; C30; C31; C32] c) 0) then b_new else (place' c alive b_new)
      | C22 => if( beq_nat (rec_num_nei' b_old [C11; C12; C13; C21; C23; C31; C32; C33] c) 0) then b_new else (place' c alive b_new)
      | C23 => if( beq_nat (rec_num_nei' b_old [C12; C13; C22; C32; C33] c) 0) then b_new else (place' c alive b_new)
      | C30 => if( beq_nat (rec_num_nei' b_old [C20; C21; C31]  c) 0) then b_new else (place' c alive b_new)
      | C31 => if( beq_nat (rec_num_nei' b_old [C20; C21; C22; C30; C32] c) 0) then b_new else (place' c alive b_new)
      | C32 => if( beq_nat (rec_num_nei' b_old [C21; C22; C23; C31; C33] c) 0) then b_new else (place' c alive b_new)
      | C33 => if( beq_nat (rec_num_nei' b_old [C22; C23; C32] c) 0) then b_new else (place' c alive b_new)
      end
  end.

Fixpoint update' (b_old: board')(b_new: board')(c: list cell): board' :=
  match c with
  | nil => b_new
  | h :: t => update' b_old (apply_rules' b_old b_new h) t
  end.

CoFixpoint do_play_game (b: board') : board' :=
  do_play_game (update' b b all_cells).

Definition play_game (

Compute play_game list10
*)


(* functions that may be used later *)
(*
Definition spread_rule (b: board) (c: cell) : board :=
  match (get b c) with
  | alive => b
  | dead => match c with
                  | C00 => if( beq_nat (rec_num_nei b [C01; C10; C11] c) 0) then b else (place c alive b)
                  | C01 => b01
                  | C02 => b02
                  | C03 => b03
                  | C10 => b10
                  | C11 => b11
                  | C12 => b12
                  | C13 => b13
                  | C20 => b20
                  | C21 => b21
                  | C22 => b22
                  | C23 => b23
                  | C30 => b30
                  | C31 => b31
                  | C32 => b32
                  | C33 => b33
                  end
  end.
*)

(*
Definition num_neighbors (b: board) (c: cell) : nat :=
match b with
  | mk_board b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 b33 => 
      match c with
      | C00 => rec_num_nei b 
      | C01 => b01
      | C02 => b02
      | C03 => b03
      | C10 => b10
      | C11 => b11
      | C12 => b12
      | C13 => b13
      | C20 => b20
      | C21 => b21
      | C22 => b22
      | C23 => b23
      | C30 => b30
      | C31 => b31
      | C32 => b32
      | C33 => b33
      end
  end.
*)