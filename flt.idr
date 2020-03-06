--created by Semen Trapeznikov M3339

module Main

import Data.Fin

%default total

-- Not Divides from last task

data not_divides : Nat -> Nat -> Type where
    not_divides_base : LT (S m) (S (S n)) -> not_divides (S m) (S (S n))
    not_divides_custom : not_divides (S m) (S (S n)) -> not_divides ((S m) + (S (S n))) (S (S n))

Uninhabited (not_divides Z n) where
    uninhabited not_divides_base impossible

Uninhabited (not_divides m Z) where
    uninhabited not_divides_base impossible

-- Divides

data divides : Nat -> Nat -> Type where
    divides_base : (m : Nat) -> n = m * (S l) -> divides (S l) n

-- Prime

data prime : Nat -> Type where
    prime_base : GT m 1 -> ((d : Nat) -> divides d m -> Either (d = 1) (d = m)) -> prime m

-- Coprime

data coprime : Nat -> Nat -> Type where
    coprime_base : (m : Nat) -> (n : Nat) -> ((d : Nat) -> divides d m -> Either (d = 1) (not_divides n d)) -> coprime m n

-- Some module operations

-- Let Fin = Nat with module ... i think you understand what i mean

--data Fin : Nat -> Type where
--    FZ : Fin (S k)
--    FS : Fin k -> Fin (S k)

is_a_eq_b : (a : Fin n) -> (b : Fin m) -> Bool
is_a_eq_b FZ FZ = True
is_a_eq_b (FS k) (FS l) = is_a_eq_b k l
is_a_eq_b _ _ = False

replicate : (init : Nat) -> (times : Nat) -> (start : Fin init) -> Fin (times + init)
replicate i Z x = x
replicate i (S n) x = FS (replicate i n x)

--Increments value with same module

-- There is a bug with rewriting of case clause,
-- so lets use with block instead

inc_fin : (n : Nat) -> (a : Fin n) -> Fin n
inc_fin (S Z) FZ = FZ
inc_fin (S (S l)) FZ = FS FZ
inc_fin (S (S l)) (FS k) with (inc_fin (S l) k)
    | FZ = FZ
    | (FS t) = FS (FS t)

inc : {n : Nat} -> (a : Fin n) -> Fin n
inc {n} a = inc_fin n a

-- Convertion without Maybe

nat_to_fin : Nat -> (n : Nat) -> Fin (S n)
nat_to_fin v Z = FZ
nat_to_fin Z (S n) = FZ
nat_to_fin (S v) (S n) = FS (nat_to_fin v n)

-- Sums numbers with same module

plus_fin : (n : Nat) -> (a, b : Fin n) -> Fin n
plus_fin (S n) FZ b = b
plus_fin (S n) a FZ = a
plus_fin (S (S n)) (FS a) (FS b) = inc (inc (weaken (plus_fin (S n) a b)))

fplus : {n : Nat} -> (a, b : Fin n) -> Fin n
fplus {n} a b = plus_fin n a b

-- Multiply numbers with same module
--(a + 1) * (b + 1) == a * b + a + b + 1

mult_fin : (n : Nat) -> (a, b : Fin n) -> Fin n
mult_fin (S n) FZ b = FZ
mult_fin (S n) a FZ = FZ 
mult_fin (S (S n)) (FS a) (FS b) = inc (weaken (fplus (mult_fin (S n) a b) (fplus a b)))

fmult : {n : Nat} -> (a, b : Fin n) -> Fin n
fmult {n} a b = mult_fin n a b

-- Power of Fin

power_fin : (n : Nat) -> (a : Fin (S (S n))) -> (b : Nat) -> Fin (S (S n))
power_fin n FZ b = FZ
power_fin n a Z = FS FZ
power_fin n a (S b) = fmult (power_fin n a b) a

fpower : {n : Nat} -> (a : Fin (S (S n))) -> (b : Nat) -> Fin (S (S n))
fpower {n} a b = power_fin n a b

-- Inc properties

inc_is_succ : (n : Nat) -> (a : Fin n) -> 
    FS a = inc_fin (S n) (weaken a)
inc_is_succ (S n) FZ = Refl
inc_is_succ (S (S n)) (FS FZ) = Refl
inc_is_succ (S (S n)) (FS a) = rewrite sym (inc_is_succ (S n) a) in Refl

-- Plus properties

plus_zero_left : (right : Fin (S n)) -> fplus FZ right = right
plus_zero_left right = Refl

plus_zero_right : (left : Fin (S n)) -> fplus left FZ = left
plus_zero_right FZ = Refl
plus_zero_right (FS left) = Refl

plus_commutative_step : (a : Fin (S n)) -> (b : Fin (S n)) ->
    (fplus a b = fplus b a) -> (fplus (FS a) (FS b) = fplus (FS b) (FS a))
plus_commutative_step a b p = rewrite p in Refl

plus_commutative : (n : Nat) -> (a : Fin n) -> (b : Fin n) ->
    fplus a b = fplus b a
plus_commutative (S n) a FZ = rewrite sym (plus_zero_right a) in Refl
plus_commutative (S n) FZ b = rewrite plus_zero_right b in Refl
plus_commutative (S (S n)) (FS a) (FS b) = plus_commutative_step a b (plus_commutative (S n) a b)

plus_associative : (n : Nat) -> (a : Fin n) -> (b : Fin n) -> (c : Fin n) ->
    fplus a (fplus b c) = fplus (fplus a b) c
plus_associative (S n) FZ b c = Refl
plus_associative (S n) a FZ c = rewrite plus_zero_right a in Refl
plus_associative (S n) a b FZ = rewrite plus_zero_right (fplus a b) in
    rewrite sym (plus_zero_right b) in Refl
plus_associative (S (S n)) (FS a) (FS b) (FS c) = believe_me "hard, lets do it later"

plus_one_eq_inc : (n : Nat) -> (a : Fin (S (S n))) ->
    inc a = fplus (FS FZ) a
plus_one_eq_inc n FZ = Refl
plus_one_eq_inc Z (FS FZ) = Refl
plus_one_eq_inc (S n) (FS a) = rewrite sym (inc_is_succ (S (S n)) a) in Refl

plus_incs_left : (n : Nat) -> (a : Fin n) -> (b : Fin n) ->
    inc (fplus a b) = fplus (inc a) b
plus_incs_left (S Z) a FZ = rewrite plus_zero_right (inc a) in
    rewrite sym (plus_zero_right a) in Refl
plus_incs_left (S (S n)) a b = rewrite plus_one_eq_inc n a in
    rewrite sym (plus_associative (S (S n)) (FS FZ) a b) in
    rewrite sym (plus_one_eq_inc n (fplus a b)) in Refl

plus_incs_right : (n : Nat) -> (a : Fin n) -> (b : Fin n) ->
    inc (fplus a b) = fplus a (inc b)
plus_incs_right (S Z) FZ b = Refl
plus_incs_right (S (S n)) a b = rewrite plus_one_eq_inc n b in
    rewrite plus_commutative (S (S n)) (FS FZ) b in
    rewrite plus_associative (S (S n)) a b (FS FZ) in
    rewrite plus_commutative (S (S n)) (fplus a b) (FS FZ) in
    rewrite sym (plus_one_eq_inc n (fplus a b)) in Refl

plus_incs : (n : Nat) -> (a : Fin n) -> (b : Fin n) ->
    inc (inc (fplus a b)) = fplus (inc a) (inc b)
plus_incs n a b = rewrite sym (plus_incs_left n a (inc b)) in
    rewrite sym (plus_incs_right n a b) in Refl

-- Mult properties

mult_zero_left : (right : Fin (S n)) -> fmult FZ right = FZ
mult_zero_left right = Refl

mult_zero_right : (left : Fin (S n)) -> fmult left FZ = FZ
mult_zero_right FZ = Refl
mult_zero_right (FS left) = Refl

mult_commutative : (n : Nat) -> (left : Fin n) -> (right : Fin n) -> 
    fmult left right = fmult right left
mult_commutative (S n) FZ right = rewrite mult_zero_right right in Refl
mult_commutative (S n) left FZ = rewrite sym (mult_zero_right left) in Refl
mult_commutative (S (S n)) (FS left) (FS right) = rewrite mult_commutative (S n) left right in
    rewrite plus_commutative (S n) left right in Refl

mult_neutral_right : (n : Nat) -> (a : Fin (S (S n))) -> a = fmult a (FS FZ)
mult_neutral_right n FZ = Refl
mult_neutral_right n (FS a) = rewrite plus_zero_right a in
    rewrite mult_zero_right a in
    rewrite inc_is_succ (S n) a in Refl

mult_neutral_left : (n : Nat) -> (a : Fin (S (S n))) -> a = fmult (FS FZ) a
mult_neutral_left n FZ = Refl
mult_neutral_left n (FS a) = rewrite inc_is_succ (S n) a in Refl

mult_succ_left : (n : Nat) -> (a : Fin (S (S n))) -> (b : Fin (S (S n))) ->
    fplus (fmult a b) b = fmult (fplus a (FS FZ)) b
mult_succ_left n a FZ = rewrite mult_zero_right a in
    rewrite sym (mult_zero_right (fplus a (FS FZ))) in Refl
mult_succ_left n FZ b = rewrite sym (mult_neutral_left n b) in Refl
mult_succ_left n (FS a) (FS b) = believe_me "parsing cases is hard"

mult_distributes_over_plus_right : (n : Nat) -> (left : Fin n) -> (centre : Fin n) -> (right : Fin n) ->
    fmult left (fplus centre right) = fplus (fmult left centre) (fmult left right)
mult_distributes_over_plus_right (S n) FZ centre right = Refl
mult_distributes_over_plus_right (S n) left FZ right = rewrite mult_zero_right left in Refl
mult_distributes_over_plus_right (S n) left centre FZ = rewrite mult_zero_right left in
    rewrite plus_zero_right (fmult left centre) in
        rewrite sym (plus_zero_right centre) in Refl
mult_distributes_over_plus_right (S (S n)) (FS left) (FS centre) (FS right) = believe_me "my head gonna break"
--    rewrite plus_associative (S n) (fmult left centre) left centre in
--    rewrite plus_associative (S n) (fmult left right) left right in
--    rewrite sym (plus_incs (S (S n)) (weaken (plus_fin (S n) (plus_fin (S n) (mult_fin (S n) left centre) left) centre)) (weaken (plus_fin (S n) (plus_fin (S n) (mult_fin (S n) left right) left) right))) in Refl
-- a * (b + c) = (a * b) + (a * c)
-- ((a + 1) * (b + 1)) + ((a + 1) * (c + 1))
-- (inc (a * b + (a + b))) + (inc (a * c + (a + c)))
-- (inc (a * b + a + b)) + (inc (a * c + a + c))
-- inc (inc ((a * b + a + b) + (a * c + a + c)))
-- ...
-- inc (inc (a * b + a * c + a + b + a + c))
-- ...
-- a * b + a * c + a + b + a + c + 1 + 1
-- a * (b + c) + a + b + a + c + 1 + 1
-- (a + 1) * ((b + 1) + (c + 1))

mult_distributes_over_plus_left : (n : Nat) -> (left : Fin n) -> (centre : Fin n) -> (right : Fin n) ->
    fmult (fplus left centre) right = fplus (fmult left right) (fmult centre right)
mult_distributes_over_plus_left (S n) left centre right = 
    rewrite mult_commutative (S n) (fplus left centre) right in
    rewrite mult_commutative (S n) left right in
    rewrite mult_commutative (S n) centre right in
    mult_distributes_over_plus_right (S n) right left centre

mult_associative : (n : Nat) -> (left : Fin n) -> (centre : Fin n) -> (right : Fin n) -> 
    fmult left (fmult centre right) = fmult (fmult left centre) right
mult_associative (S n) FZ centre right = Refl
mult_associative (S n) left FZ right = rewrite mult_zero_right left in Refl
mult_associative (S n) left centre FZ = believe_me "i will write it sometimes"
mult_associative (S (S n)) (FS FZ) (FS FZ) (FS FZ) = Refl
mult_associative (S (S (S n))) (FS left) (FS centre) (FS right) = believe_me "ääääääääääääääääääääääää"
--    rewrite plus_one_eq_inc (S n) (weaken (plus_fin (S (S n)) (mult_fin (S (S n)) left centre) (plus_fin (S (S n)) left centre))) in
--    rewrite mult_distributes_over_plus_left (S (S (S n))) (FS FZ) (weaken (plus_fin (S (S n)) (mult_fin (S (S n)) left centre) (plus_fin (S (S n)) left centre))) (FS right) in
--    rewrite sym (inc_is_succ (S (S n)) right) in
--    Refl

-- ((FS left) * (FS centre)) * (FS right)
-- (inc (weaken (left * centre) + (left + centre))) * (FS right) * (FS right)
-- (inc weaken right) + ((weaken (left * cente + (left + centre))) * (FS right))
-- (FS right) + ((weaken (left * cente + (left + centre))) * (FS right))
-- want
-- (FS left) * ((FS centre) * (FS right))

-- Power properties

power_of_one : (n : Nat) -> (b : Nat) -> (FS FZ) = power_fin n (FS FZ) b
power_of_one n Z = Refl
power_of_one n (S b) = rewrite sym (power_of_one n b) in Refl

lemma_a_power_km : (n : Nat) -> (a : Fin (S (S n))) -> (k : Nat) -> (m : Nat) -> 
    (fpower a k = (FS FZ)) -> FS FZ = fpower (fpower a k) m
lemma_a_power_km n a k m p = 
    rewrite p in
    rewrite power_of_one n m in
    Refl

-- Convertion properties

n_to_fin_n : (n : Nat) -> FZ = nat_to_fin n n
n_to_fin_n n = Refl
