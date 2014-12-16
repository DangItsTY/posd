Inductive mark : Set :=
  | alive : mark
  | dead : mark.

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

Inductive board := 
  mk_board: mark -> mark -> mark -> mark -> 
            mark -> mark -> mark -> mark -> 
            mark -> mark -> mark -> mark -> 
            mark -> mark -> mark -> mark -> board.

Example emptyboard := mk_board dead dead dead dead 
                           dead dead dead dead
                           dead dead dead dead
                           dead dead dead dead.

Compute emptyboard.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

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

Compute place C00 alive emptyboard.
Compute place C23 alive emptyboard.

Fixpoint initialize (b : board) (l : list cell) : board :=
  match l with
  | nil => b
  | cons h t => initialize (place h alive b) t
  end.

Example mylist := cons C00 (cons C01(cons C02 nil)).

Compute initialize emptyboard mylist.

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
      
Example all_cells := [C00; C01; C02; C03; C10; C11; C12; C13; C20; C21; C22; C23; C30; C31; C32; C33].

Notation "x :: l" := (cons x l) (at level 60, right associativity).

Fixpoint rec_num_nei (b:board) (l: list cell) (c: cell) : nat :=
  match l with
  | nil => 0
  | h :: t => match (get b h) with
              | alive => S (rec_num_nei b t c)
              | dead => (rec_num_nei b t c)
              end
  end.

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

Fixpoint update (b_old: board)(b_new: board)(c: list cell): board :=
  match c with
  | nil => b_new
  | h :: t => update b_old (apply_rules b_old b_new h) t
  end.

Definition list10 := [C01].
Compute initialize emptyboard list10.

Compute update (initialize emptyboard list10) emptyboard all_cells.


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



Definition list_fancy := [C00; C01; C02; C10; C12; C20; C21; C22].
Example test_list_fancy : rec_num_nei emptyboard list_fancy C11 = 0.
Proof. reflexivity. Qed.

Definition b10 := mk_board alive alive alive dead alive alive alive dead alive alive alive dead dead dead dead dead.
Example test_b10 : rec_num_nei b10 list_fancy C11 = 8.
Proof. reflexivity. Qed.



