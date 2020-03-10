--created by Semen Trapeznikov M3339
--final answers are in the end of file

module Main

%default total

--variant 2

data L_E : (m : Nat) -> (n : Nat) -> Type where
    L_E_zero : L_E Z n
    L_E_custom : L_E m n -> L_E (S m) (S n)

Uninhabited (L_E (S n) Z) where
    uninhabited L_E_zero impossible

not_equal : {m : Nat} -> {n : Nat} -> (m = n -> Void) -> (n = m -> Void)
not_equal pr tp = pr (sym tp)

invalid_L_E : Not (L_E (S a) Z)
invalid_L_E L_E_zero impossible

proof_x_L_E_x : (m : Nat) -> L_E m m
proof_x_L_E_x Z = L_E_zero
proof_x_L_E_x (S m) = L_E_custom (proof_x_L_E_x m)

proof_L_E_example : L_E 2 5
proof_L_E_example = L_E_custom (L_E_custom L_E_zero)

repeat : {a : Type} -> (times : Nat) -> (f : a -> a) -> (init : a) -> a
repeat Z f i = i
repeat (S t) f i = f (repeat t f i)

proof_triangle : (n : Nat) -> (m : Nat) -> (p : Nat) -> L_E n m -> L_E m p -> L_E n p
proof_triangle Z m p x y = L_E_zero
proof_triangle (S n) (S m) (S p) (L_E_custom x) (L_E_custom y) = L_E_custom (proof_triangle n m p x y)

bool_L_E : (a : Nat) -> (b : Nat) -> Bool
bool_L_E Z b = True
bool_L_E a Z = False
bool_L_E (S a) (S b) = bool_L_E a b

proof_L_E_add : (a : Nat) -> (b : Nat) -> L_E a (a + b)
proof_L_E_add Z b = L_E_zero
proof_L_E_add (S a) b = L_E_custom (proof_L_E_add a b)

proof_L_E_add_r : (a : Nat) -> (b : Nat) -> L_E b (a + b)
proof_L_E_add_r a Z = L_E_zero
proof_L_E_add_r a (S b) = rewrite sym (plusSuccRightSucc a b) in L_E_custom (proof_L_E_add_r a b)

proof_L_E_reduce : L_E (S a) (S b) -> L_E a b
proof_L_E_reduce (L_E_custom p) = p

is_L_E : (a : Nat) -> (b : Nat) -> Dec (L_E a b)
is_L_E Z b = Yes L_E_zero
is_L_E (S a) Z = No invalid_L_E
is_L_E (S a) (S b) with (is_L_E a b)
    is_L_E (S a) (S b) | (Yes p) = Yes (L_E_custom p)
    is_L_E (S a) (S b) | (No p2) = No (p2 . proof_L_E_reduce)

proof_any_pair : (a : Nat) -> (b : Nat) -> (x : Nat ** ((L_E a x), (L_E b x)))
proof_any_pair a b = ((a + b) ** ((proof_L_E_add a b), (proof_L_E_add_r a b)))

--variant 6

data n_d : (m : Nat) -> (n : Nat) -> Type where
    n_d_base : Not((S m) = (S (S n))) -> L_E (S m) (S (S n)) -> n_d (S m) (S (S n))
    n_d_custom : n_d (S m) (S (S n)) -> n_d ((S m) + (S (S n))) (S (S n))

Uninhabited (n_d Z n) where
    uninhabited n_d_base impossible

Uninhabited (n_d m Z) where
    uninhabited n_d_base impossible

proof_non_simm_right : (n_d (S (S Z)) (S Z)) -> Void
proof_non_simm_right n_d_base impossible

proof_one_ne_two : Not ((S Z) = (S (S Z)))
proof_one_ne_two Refl impossible

proof_one_le_two : L_E (S Z) (S (S Z))
proof_one_le_two = L_E_custom L_E_zero

proof_non_simm_left : (n_d (S Z) (S (S Z)))
proof_non_simm_left = n_d_base proof_one_ne_two proof_one_le_two

--

--@(a:N0).@(b:N0).@(c:N0).a<=b -> a<=c -> ?(d:N0).b<=d & c<=d
proof_rhombus : (a : Nat) -> (b : Nat) -> (c : Nat) -> (b = c -> Void) -> L_E a b -> L_E a c -> (x : Nat ** Pair (L_E b x) (L_E c x))
proof_rhombus a b c ne left right = proof_any_pair b c

--let (!/) := a mod b != 0
--?(a:N0).?(b:N0).a !/ b & !(a !/ b)
proof_non_simm : (p : (Nat, Nat) ** ((n_d (fst p) (snd p)), (Not (n_d (snd p) (fst p)))))
proof_non_simm = (((S Z), (S (S Z))) ** (proof_non_simm_left, proof_non_simm_right))
