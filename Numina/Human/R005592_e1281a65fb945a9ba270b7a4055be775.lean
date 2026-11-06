import Mathlib

open Nat List
/-Compute the decimal expansion of $\sqrt{\pi}$. Your score will be $\min (23, k)$, where $k$ is the number of consecutive correct digits immediately following the decimal point in your answer.-/


-- Helper function to get pairs of digits from an integer N_val
-- Example: 12345 -> [1, 23, 45]
-- Example: 123456 -> [12, 34, 56]
def get_digit_pairs_from_int (N_val : ℕ) : List ℕ :=
  if N_val = 0 then [0] else
  let s_digits := (Nat.digits 10 N_val).reverse -- Digits in correct order
  if h_empty : s_digits = [] then
    [0] -- Should not happen if N_val > 0, but as a safeguard
  else
    let rec make_pairs_from_even_list (l : List ℕ) : List ℕ :=
      match l with
      | [] => []
      | d1 :: d2 :: ds => (d1 * 10 + d2) :: make_pairs_from_even_list ds
      | _ :: [] => panic! "make_pairs_from_even_list called with odd length list" -- Should not happen with correct logic
    if s_digits.length % 2 = 1 then -- Odd number of digits
      s_digits.head h_empty :: make_pairs_from_even_list (s_digits.tail)
    else -- Even number of digits
      make_pairs_from_even_list s_digits

-- Function to calculate digits of the square root (pure functional version)
def calculate_sqrt_digits (X : ℕ) : List ℕ :=
  let digit_pairs := get_digit_pairs_from_int X
  if digit_pairs.isEmpty then [] else -- Should not happen if X > 0

  -- Helper function to find the largest d in 0..9 satisfying the condition
  let find_d_digit (P_current : ℕ) (C_current : ℕ) : ℕ :=
    let X_trial := P_current * 20
    let check_condition (d : ℕ) : Bool :=
      if P_current = 0 then d * d ≤ C_current
      else d * (X_trial + d) ≤ C_current
    -- Iterate d from 9 down to 0 and take the first one that satisfies the condition
    match (List.range 10).reverse.find? check_condition with
    | some d_val => d_val
    | none       => 0 -- Should always find at least d=0 if C_current is non-negative

  -- The state for foldl is (P_val : ℕ, R_val : ℕ, accumulated_digits : List ℕ)
  let initial_state : (ℕ × ℕ × List ℕ) := (0, 0, [])

  let process_pair (state : ℕ × ℕ × List ℕ) (current_pair : ℕ) : (ℕ × ℕ × List ℕ) :=
    let (P_old, R_old, digits_acc) := state
    let C := R_old * 100 + current_pair
    let d_found := find_d_digit P_old C

    let X_trial_for_Y_sub := P_old * 20 -- Use P_old for calculating Y_sub
    let Y_sub := if P_old = 0 then d_found * d_found else d_found * (X_trial_for_Y_sub + d_found)

    let P_new := P_old * 10 + d_found
    let R_new := C - Y_sub -- Nat subtraction, assumes C ≥ Y_sub which should hold by d_found logic
    let new_digits_acc := digits_acc.concat d_found
    (P_new, R_new, new_digits_acc)

  let final_state := digit_pairs.foldl process_pair initial_state
  final_state.2.2 -- Extract the list of digits (the third component of the triple)

def pi_scaled_N : ℕ :=
  314159265358979323846264338327950288419716939

-- Calculate the digits
def sqrt_pi_digits_list : List ℕ := calculate_sqrt_digits pi_scaled_N

-- The computed digits for sqrt(pi)
theorem number_theory_609021 :
  Nat.ofDigits 10  sqrt_pi_digits_list.reverse = 17724538509055160272981 := by 
    native_decide