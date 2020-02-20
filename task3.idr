--created by Semen Trapeznikov M3339
--final answers are in the end of file

module Main

%default total

--All x(N0).(2x + 1)^2 = 4x^2 + 4x + 1
--mult ((mult 2 x) + 1) ((mult 2 x) + 1) = (mult 4 (mult x x)) + (mult 4 x) + 1
--mult ((x + (x + 0)) + 1) ((x + (x + 0)) + 1) 
--                 = ((mult x x) + ((mult x x) + ((mult x x) + ((mult x x) + 0)))) + (x + (x + (x + (x + 0)))) + 1

commute_abc : (a : Nat) -> (b : Nat) -> a + b = c -> b + a = c
commute_abc a b p = rewrite plusCommutative b a in p

move_out_right : (k : Nat) -> (n : Nat) -> k + (S n) = S(k + n) --S k + S n = S(S k + n)
move_out_right Z n = Refl
move_out_right (S k) n = rewrite move_out_right k n in Refl

move_out_left : (k : Nat) -> (n : Nat) -> (S k) + n = S(k + n) --S k + S n = S(k + S n)
move_out_left k n = Refl --useless one but good for understanding

proof_S_S_left : (n : Nat) -> (S n) + (S n) = S(S n + n) --(S S n) + (S S n) = S(S S n + S n)
proof_S_S_left Z = Refl
proof_S_S_left (S n) = rewrite move_out_right (S (S n)) (S n) in Refl

proof_S_S_right : (n : Nat) -> (S n) + (S n) = S(n + (S n)) --(S S n) + (S S n) = S(S n + S S n)
proof_S_S_right n = Refl --useless one but good for understanding

proof_S_S : (n : Nat) -> (S n) + (S n) = S (S (n + n))  
-- (S (S n)) + (S (S n)) = S (S ((S n) + (S n))) -> (S (S n)) + (S (S n)) = S(S S n + S n)
proof_S_S Z = Refl
proof_S_S (S n) = rewrite move_out_right (S (S n)) (S n) in Refl

proof_mult_two_N : (n : Nat) -> mult 2 n = n + n -- open mult -> n+(n+0)=n+n ||n+1 -> mult 2 (S n) = (S n) + (S n)
proof_mult_two_N n = rewrite plusAssociative n n Z in plusZeroRightNeutral (n + n)

proof_mult_two_sums : (a : Nat) -> (b : Nat) -> (c : Nat) -> (d : Nat) -> (mult (a + b) (c + d)) = ((mult a c) + (mult b c)) + ((mult a d) + (mult b d))
proof_mult_two_sums a b c d = rewrite sym (multDistributesOverPlusLeft a b d) in
    (rewrite sym (multDistributesOverPlusLeft a b c) in 
    multDistributesOverPlusRight (a + b) c d) --(a + b) * c + (a + b) * d

proof_sum_combine_sides : (a : Nat) -> (b : Nat) -> (c : Nat) -> (d : Nat) -> ((a + b) + c) + d = (a + b) + (c + d)
proof_sum_combine_sides a b c d = rewrite plusAssociative (a + b) c d in Refl

proof_sum_combine_middle : (a : Nat) -> (b : Nat) -> (c : Nat) -> (d : Nat) -> ((a + b) + c) + d = a + (b + c) + d
proof_sum_combine_middle a b c d = rewrite sym (plusAssociative a b c) in Refl

proof_sum_square_one : (a : Nat) -> (b : Nat) -> mult (a + b) (a + b) = (((mult a a) + (mult b a)) + (mult a b)) + (mult b b)
proof_sum_square_one a b = rewrite proof_sum_combine_sides (mult a a) (mult b a) (mult a b) (mult b b) in proof_mult_two_sums a b a b

proof_sum_square_two : (a : Nat) -> (b : Nat) -> mult (a + b) (a + b) = (mult a a) + ((mult b a) + (mult a b)) + (mult b b)
proof_sum_square_two a b = rewrite sym (proof_sum_combine_middle (mult a a) (mult b a) (mult a b) (mult b b)) in proof_sum_square_one a b

proof_normalize_sum_of_mults : (a : Nat) -> (b : Nat) -> (mult a b + mult a b) = (mult b a + mult a b)
proof_normalize_sum_of_mults a b = rewrite multCommutative a b in Refl

proof_sum_square_three : (a : Nat) -> (b : Nat) -> mult (a + b) (a + b) = (mult a a) + ((mult a b) + (mult a b)) + (mult b b)
proof_sum_square_three a b = rewrite proof_normalize_sum_of_mults a b in proof_sum_square_two a b

proof_sum_square : (a : Nat) -> (b : Nat) -> mult (a + b) (a + b) = (mult a a) + (mult 2 (mult a b)) + (mult b b)
proof_sum_square a b = rewrite proof_mult_two_N (mult a b) in proof_sum_square_three a b

proof_double_double_x_one : (x : Nat) -> plus (plus x x) (plus (plus x x) 0) = plus (plus x (plus x 0)) (plus (plus x (plus x 0)) 0)
proof_double_double_x_one x = rewrite sym (plusZeroRightNeutral x) in Refl

proof_double_double_x_two_one : (x : Nat) -> plus (plus x x) (plus x (plus x 0)) = plus (plus x x) (plus (plus x x) 0)
proof_double_double_x_two_one x = rewrite plusAssociative x x 0 in Refl

proof_double_double_x_two : (x : Nat) -> plus (plus x x) (plus x (plus x 0)) = plus (plus x (plus x 0)) (plus (plus x (plus x 0)) 0)
proof_double_double_x_two x = rewrite proof_double_double_x_two_one x in proof_double_double_x_one x

proof_double_double_x_three : (x : Nat) -> plus x (plus x (plus x (plus x 0))) = plus (plus x x) (plus x (plus x 0))
proof_double_double_x_three x = rewrite plusAssociative x x (plus x (plus x 0)) in Refl

proof_double_double_x : (x : Nat) -> mult 4 x = mult 2 (mult 2 x) --plus (plus x (plus x 0)) (plus (plus x (plus x 0)) 0)
proof_double_double_x x = rewrite proof_double_double_x_three x in proof_double_double_x_two x

proof_four_mul_x_one : (x : Nat) -> (mult 2 (mult 2 x)) = (mult 2 (mult (mult 2 x) 1))
proof_four_mul_x_one x = rewrite sym (multOneRightNeutral (mult 2 x)) in Refl

proof_four_mul_x : (x : Nat) -> (mult 4 x) = (mult 2 (mult (mult 2 x) 1))
proof_four_mul_x x = rewrite proof_double_double_x x in proof_four_mul_x_one x

--

proof_two_x_square_one : (x : Nat) -> (mult (x + x) (x + x)) = (mult (mult 2 x) (mult 2 x))
proof_two_x_square_one x = rewrite sym (plusZeroRightNeutral x) in Refl

proof_two_x_square_two : (x : Nat) -> ((mult x x) + (mult x x)) + ((mult x x) + (mult x x)) = (mult (x + x) (x + x))
proof_two_x_square_two x = rewrite proof_mult_two_sums x x x x in Refl

proof_two_x_square_three : (x : Nat) -> (x + (x + (x + x))) = (x + (x + (x + (x + 0))))
proof_two_x_square_three x = rewrite sym (plusZeroRightNeutral x) in Refl

proof_two_x_square_four : (x : Nat) -> (x + x) + (x + x) = (x + (x + (x + x)))
proof_two_x_square_four x = rewrite sym (plusAssociative x x (x + x)) in Refl

proof_two_x_square_five : (x : Nat) -> ((mult x x) + (mult x x)) + ((mult x x) + (mult x x)) = (mult (mult 2 x) (mult 2 x))
proof_two_x_square_five x = rewrite proof_two_x_square_two x in proof_two_x_square_one x

proof_two_x_square_six : (x : Nat) -> (x + (x + (x + (x + 0)))) = (x + x) + (x + x)
proof_two_x_square_six x = rewrite sym (proof_two_x_square_three x) in sym (proof_two_x_square_four x)

proof_two_x_square_seven : (x : Nat) -> ((mult x x) + ((mult x x) + ((mult x x) + ((mult x x) + 0)))) = ((mult x x) + (mult x x)) + ((mult x x) + (mult x x))
proof_two_x_square_seven x = proof_two_x_square_six (mult x x)

proof_two_x_square : (x : Nat) -> (mult 4 (mult x x)) = (mult (mult 2 x) (mult 2 x))
proof_two_x_square x = rewrite proof_two_x_square_seven x in proof_two_x_square_five x

--

proof_task_appl : (x : Nat) -> mult ((mult 2 x) + 1) ((mult 2 x) + 1) = (mult (mult 2 x) (mult 2 x)) + (mult 2 (mult (mult 2 x) 1)) + 1
proof_task_appl x = rewrite proof_sum_square (mult 2 x) 1 in Refl

proof_task_appl_one : (x : Nat) -> mult ((mult 2 x) + 1) ((mult 2 x) + 1) = (mult (mult 2 x) (mult 2 x)) + (mult 4 x) + 1
proof_task_appl_one x = rewrite proof_four_mul_x x in proof_task_appl x

--@(x:N0).(2x + 1)^2 = 4x^2 + 4x + 1
proof_task : (x : Nat) -> mult (mult 2 x + 1) (mult 2 x + 1) = mult 4 (mult x x) + (mult 4 x) + 1
proof_task x = rewrite proof_two_x_square x in proof_task_appl_one x

--@(x:N0).x^2 + x^2 + x^2 + x^2 = (2x)^2
proof_task_2 : (x : Nat) -> (mult x x) + (mult x x) + (mult x x) + (mult x x) = mult (mult 2 x) (mult 2 x)
proof_task_2 x = rewrite sym (plusAssociative ((mult x x) + (mult x x)) (mult x x) (mult x x)) in proof_two_x_square_five x
