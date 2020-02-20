--created by Semen Trapeznikov M3339
--final answers are in the end of file

module Main

%default total

--variant 2

data l_e : (m : Nat) -> (n : Nat) -> Type where
    l_e_zero : l_e Z n
    l_e_custom : l_e m n -> l_e (S m) (S n)

Uninhabited (l_e (S n) Z) where
    uninhabited l_e_zero impossible

not_equal : {m : Nat} -> {n : Nat} -> (m = n -> Void) -> (n = m -> Void)
not_equal pr tp = pr (sym tp)

invalid_l_e : Not (l_e (S a) Z)
invalid_l_e l_e_zero impossible

proof_x_l_e_x : (m : Nat) -> l_e m m
proof_x_l_e_x Z = l_e_zero
proof_x_l_e_x (S m) = l_e_custom (proof_x_l_e_x m)

proof_l_e_example : l_e 2 5
proof_l_e_example = l_e_custom (l_e_custom l_e_zero)

repeat : {a : Type} -> (times : Nat) -> (f : a -> a) -> (init : a) -> a
repeat Z f i = i
repeat (S t) f i = f (repeat t f i)

proof_triangle : (n : Nat) -> (m : Nat) -> (p : Nat) -> l_e n m -> l_e m p -> l_e n p
proof_triangle Z m p x y = l_e_zero
proof_triangle (S n) (S m) (S p) (l_e_custom x) (l_e_custom y) = l_e_custom (proof_triangle n m p x y)

bool_l_e : (a : Nat) -> (b : Nat) -> Bool
bool_l_e Z b = True
bool_l_e a Z = False
bool_l_e (S a) (S b) = bool_l_e a b

proof_l_e_add : (a : Nat) -> (b : Nat) -> l_e a (a + b)
proof_l_e_add Z b = l_e_zero
proof_l_e_add (S a) b = l_e_custom (proof_l_e_add a b)

proof_l_e_add_r : (a : Nat) -> (b : Nat) -> l_e b (a + b)
proof_l_e_add_r a Z = l_e_zero
proof_l_e_add_r a (S b) = rewrite sym (plusSuccRightSucc a b) in l_e_custom (proof_l_e_add_r a b)

proof_l_e_reduce : l_e (S a) (S b) -> l_e a b
proof_l_e_reduce (l_e_custom p) = p

is_l_e : (a : Nat) -> (b : Nat) -> Dec (l_e a b)
is_l_e Z b = Yes l_e_zero
is_l_e (S a) Z = No invalid_l_e
is_l_e (S a) (S b) with (is_l_e a b)
    is_l_e (S a) (S b) | (Yes p) = Yes (l_e_custom p)
    is_l_e (S a) (S b) | (No p2) = No (p2 . proof_l_e_reduce)

proof_any_pair : (a : Nat) -> (b : Nat) -> (x : Nat ** ((l_e a x), (l_e b x)))
proof_any_pair a b = ((a + b) ** ((proof_l_e_add a b), (proof_l_e_add_r a b)))

--variant 6

data n_d : (m : Nat) -> (n : Nat) -> Type where
    n_d_base : Not ((S m) = (S (S n))) -> l_e (S m) (S (S n)) -> n_d (S m) (S (S n))
    n_d_custom : n_d (S m) (S (S n)) -> n_d ((S m) + (S n)) (S (S n))

Uninhabited (n_d Z n) where
    uninhabited n_d_base impossible

Uninhabited (n_d m Z) where
    uninhabited n_d_base impossible

proof_non_simm_right : (n_d (S (S Z)) (S Z)) -> Void
proof_non_simm_right n_d_base impossible

proof_one_ne_two : Not ((S Z) = (S (S Z)))
proof_one_ne_two Refl impossible

proof_one_le_two : l_e (S Z) (S (S Z))
proof_one_le_two = l_e_custom l_e_zero

proof_non_simm_left : (n_d (S Z) (S (S Z)))
proof_non_simm_left = n_d_base proof_one_ne_two proof_one_le_two

--

--@(a:N0).@(b:N0).@(c:N0).a<=b -> a<=c -> ?(d:N0).b<=d & c<=d
proof_rhombus : (a : Nat) -> (b : Nat) -> (c : Nat) -> (b = c -> Void) -> l_e a b -> l_e a c -> (x : Nat ** Pair (l_e b x) (l_e c x))
proof_rhombus a b c ne left right = proof_any_pair b c

--let (!/) := a mod b != 0
--?(a:N0).?(b:N0).a !/ b & !(a !/ b)
proof_non_simm : (p : (Nat, Nat) ** ((n_d (fst p) (snd p)), (Not (n_d (snd p) (fst p)))))
proof_non_simm = (((S Z), (S (S Z))) ** (proof_non_simm_left, proof_non_simm_right))

