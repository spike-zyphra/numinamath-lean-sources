import Mathlib

/- 3. (7 points) The number 49 is written on the board. In one move, it is allowed to either double the number or erase its last digit. Is it possible to get the number 50 in several moves? -/
theorem number_theory_172704 :  ∃ a : ℕ → ℕ, a 0 = 49 ∧ (∀ n, a (n + 1) = 2 * a n ∨ a (n + 1) = a n / 10) ∧ ∃ n, a n = 50 := by
  --We prove that 50 can be produced from 49 using given operations.
  --We use the following sequence.
  let f : Nat → Nat := fun n => match n with
    | 0   => 49
    | 1   => 4
    | 2   => 8
    | 3   => 16
    | 4   => 32
    | 5   => 64
    | 6   => 128
    | 7   => 256
    | 8   => 25
    | 9   => 50
    | 10  => 5
    | n+11=> 0
  use f

  --Then, we verify that f is valid by definition.
  simp

  constructor
  intro n
  
  by_cases neq : n = 0
  rw [neq]; simp [f]
  by_cases neq : n = 1
  rw [neq]; simp [f]
  by_cases neq : n = 2
  rw [neq]; simp [f]
  by_cases neq : n = 3
  rw [neq]; simp [f]
  by_cases neq : n = 4
  rw [neq]; simp [f]
  by_cases neq : n = 5
  rw [neq]; simp [f]
  by_cases neq : n = 6
  rw [neq]; simp [f]
  by_cases neq : n = 7
  rw [neq]; simp [f]
  by_cases neq : n = 8
  rw [neq]; simp [f]
  by_cases neq : n = 9
  rw [neq]; simp [f]
  by_cases neq : n = 10
  rw [neq]; simp [f]
  have nge11: 11 ≤ n := by omega
  have exi : ∃ k : ℕ, k + 11 = n := by use n-11; omega
  obtain ⟨k,hk⟩ := exi
  have fn: f n = 0 := by 
    have : f (k+11) = 0 := by simp [f]
    rw [hk] at this ; exact this
  have exi': ∃ k': ℕ, k'+ 11 = n+1 := by use n+1 -11; omega
  obtain ⟨k',hk'⟩ := exi'
  have fnp1 : f (n+1) = 0 := by 
    have : f (k'+11) = 0 := by simp [f]
    rw [hk'] at this ; exact this
  right;
  rw [fnp1,fn]; 

  use 9
  
