import Mathlib

def a: ℤ := 327 ^ 66

-- we show the pow_mod lemma for ℤ version
lemma int.pow_mod (a b: ℤ) (n: ℕ): a ^ n % b = (a % b) ^ n % b := by
   induction' n with n ih
   .
    simp
   .
    rw [show a ^ (n + 1) = a * a ^ n by ring]
    rw [Int.mul_emod]
    rw [ih]
    rw [show (a % b) ^ (n + 1) = (a % b) * (a % b) ^ n by ring]
    set c:= a % b
    set d:= c ^ n
    rw [Int.mul_emod]
    simp
    symm
    apply Int.mul_emod

-- show the fermat's little theorem for the case when p = 17
lemma lemma_1 (n: ℤ): n ^ 8 % 17 = 0 ∨ n ^ 8 % 17 = 1 ∨ n ^ 8 % 17 = 16 := by
  rw [int.pow_mod n 17 8]
  set b:= n % 17
  have lb: b < 17 := by omega
  have rb: 0 ≤ b := by omega
  clear_value b
  by_cases s: b = 0
  .
    simp [s]
  .
    replace s: 0 < b := by omega
    right
    interval_cases b
    all_goals norm_num

lemma lemma_2 (n: ℤ): n ^ 16 % 17 = 0 ∨ n ^ 16 % 17 = 1 := by
  have f:= lemma_1 n
  rw [show n ^ 16 = (n ^ 8) ^ 2 by ring]
  rw [int.pow_mod (n ^ 8) 17 2]
  rcases f with f | f | f
  .
    simp [f]
  .
    simp [f]
  .
    simp [f]


/-Let $A$ be an integer. Determine the remainder when $A^{66} - 327^{66}$ is divided by $17$.
Show the answer is $( (A \pmod{17})^2 - 16) \pmod{17}$, where $A \pmod{17}$ is the remainder of $A$ when divided by $17$-/

theorem number_theory_641249 (A: ℤ): (A ^ 66 - a) % 17 = ((A % 17) ^ 2 - 16) % 17 := by
  rw [Int.sub_emod]
  suffices A ^ 66 % 17 = (A % 17) ^ 2 % 17 ∧ a % 17 = 16 by
    rw [this.1, this.2]
    set p:= (A % 17) ^ 2
    clear this
    clear_value p
    rw [Int.sub_emod]
    rw [show p % 17 % 17 = p % 17 by simp]
    rw [← Int.sub_emod]
  constructor

  .
    rw [show A ^ 66 = A ^ 2 * A ^ 64 by ring]
    rw [Int.mul_emod]
    have f:= lemma_2 A
    rcases f with f | f
    .
      suffices A % 17 = 0 by
        rw [show A ^ 2 % 17 = (A % 17) ^ 2 % 17 by rw [int.pow_mod A 17 2]]
        simp [this]
      rw [← Int.dvd_iff_emod_eq_zero] at f
      rw [← Int.dvd_iff_emod_eq_zero]
      apply Int.Prime.dvd_pow' at f
      simp at f
      tauto
      norm_num
    .
      suffices A ^ 64 % 17 = 1 by
        simp [this]
        rw [int.pow_mod A 17 2]
      rw [show A ^ 64 = (A ^ 16) ^ 4 by ring]
      rw [int.pow_mod (A ^ 16) 17 4]
      simp [f]

  .
    set b:= (327: ℤ) with hb
    have o: a = b ^ 66 := by
      rw [hb]
      rfl
    rw [o]
    clear o
    rw [int.pow_mod b 17 66]
    have u: b % 17 = 4 := by
      simp [hb]
    rw [u]
    set c:= (4: ℤ)
    clear hb u
    rw [show c ^ 66 = c ^ 2 * c ^ 64 by ring]
    rw [Int.mul_emod]
    suffices c ^ 2 % 17 = 16 ∧ c ^ 64 % 17 = 1 by
      simp [this]
    constructor
    .
      simp [c]
    .
      rw [show c ^ 64 = (c ^ 8) ^ 8 by ring]
      rw [int.pow_mod (c ^ 8) 17 8]
      suffices c ^ 8 % 17 = 1 by
        simp [this]
      simp [c]