import Mathlib

/- 1. Prove that the equation


$$

\frac{1}{x}-\frac{1}{y}=\frac{1}{p}, \quad p \in \mathbb{N}

$$


has a unique solution in $\mathbb{N}$ if and only if $p$ is a prime number. -/

-- the diaphantine equation 1 / a - 1 / b = 1 / c with all 3 nonzero, is equivalent to (c + b) * (c - a) = c^2
lemma l_diaphantine_iff (a b c : ℕ) (hc : c ≠ 0) : (a ≠ 0 ∧ b ≠ 0 ∧ (1 / a : ℚ) - 1 / b = 1 / c) ↔
    (a ≠ 0 ∧ b ≠ 0 ∧ (c + b) * (c - a) = c^2) := by
  simp
  rintro ha hb
  field_simp
  qify
  ring_nf
  -- to prove that the subtraction agrees from rational to nats, we have to show a ≤ c in both sides
  constructor <;> rintro h
  -- in lhs a < c as b * c = a * c + b * a and 0 < a * c
  . have : a < c := by
      replace h : (b * c : ℚ) = a * c + b * a := by linarith
      have : 0 < (a * c : ℚ) := by
        norm_cast
        apply mul_pos <;> omega
      have : b * a < (b * c : ℚ) := by linarith
      norm_cast at this
      apply Nat.lt_of_mul_lt_mul_left this
    push_cast [this]
    linarith
  -- in rhs a < c as otherwise c - a is 0, then c is 0
  . have : a < c := by
      by_contra h'
      simp at h'
      simp [h'] at h
      norm_cast at h
      rw [eq_comm] at h
      simp at h
      contradiction
    push_cast [this] at h
    linarith

-- if 1 < p then (p-1, p^2-p) is a solution for the diaphantine equation, this is used multiple times
lemma l_diaphantine_soln_of_one_lt {p : ℕ} (hp : 1 < p) : (fun xy => xy.1 ≠ 0 ∧ xy.2 ≠ 0 ∧
    (p + xy.2) * (p - xy.1) = p ^ 2) (p - 1, p ^ 2 - p) := by
  have : p < p^2 := by refine lt_self_pow₀ hp (by norm_num)
  simp
  and_intros
  . by_contra h
    omega
  . by_contra h
    omega
  . rw [show p + (p^2 - p) = p^2 by omega, show p - (p - 1) = 1 by omega]
    simp

theorem number_theory_218627 (p : ℕ) (hp : p ≠ 0) :
    (∃! xy : ℕ × ℕ, xy.1 ≠ 0 ∧ xy.2 ≠ 0 ∧ (1 / xy.1 : ℚ) - (1 / xy.2 : ℚ) = 1 / p) ↔ Nat.Prime p := by
  -- first we convert the diaphantine to a better expression using lemma 1
  convert_to (∃! xy : ℕ × ℕ, xy.1 ≠ 0 ∧ xy.2 ≠ 0 ∧ (p + xy.2) * (p - xy.1) = p^2) ↔ Nat.Prime p
  . apply existsUnique_congr
    rintro xy
    apply l_diaphantine_iff
    exact hp
  constructor <;> rintro h
  --to prove p is prime, two cases, p = 1 or  not 1, if p = 1, then there is no solution as then 1 - xy.1 = 1 and that implies xy.1 = 0, contradicting unique solution
  . by_cases hp' : p = 1
    . replace h := h.exists
      obtain ⟨xy, hx, hy, h⟩ := h
      rw [hp'] at h
      simp at h
      replace h := h.right
      have : xy.1 < 1 := by omega
      omega
    -- if p ≠ 1, then the hypothesis implies any two solutions are same, we will prove contrapositive that if p is not prime then there are two different solution
    . let F := fun (xy : ℕ × ℕ) => xy.1 ≠ 0 ∧ xy.2 ≠ 0 ∧ (p + xy.2) * (p - xy.1) = p ^ 2
      replace h (xy₁ xy₂ : ℕ × ℕ) (h1 : F xy₁) (h2 : F xy₂) : xy₁ = xy₂ := by
        apply h.unique h1 h2
      have hp'' : 2 ≤ p := by omega
      contrapose h
      push_neg
      -- first solution is (p-1, p^2 - p) by lemma
      use (p - 1, p^2 - p)
      simp [show F (p - 1, p ^ 2 - p) by apply l_diaphantine_soln_of_one_lt hp'']
      -- if p is not prime then there is nontrivial factorization a * b
      obtain ⟨a, ha', ha⟩ := Nat.exists_dvd_of_not_prime2 hp'' h
      obtain ⟨b, hab⟩ := ha'
      have hb : 2 ≤ b := by
        by_contra hb
        simp at hb
        interval_cases b <;> linarith
      -- second solution is (p-a, a*b^2 - p), due to non trivial ness this is diffferent.
      use p - a, a * b^2 - p
      simp [F]
      and_intros
      . by_contra h'
        omega
      . by_contra h'
        rw [sq, ← mul_assoc, ← hab] at h'
        have : p * b ≤ p * 1 := by omega
        have := Nat.le_of_mul_le_mul_left this (by linarith)
        linarith
      . rw [show p - (p - a) = a by omega]
        have : p < a * b ^ 2 := by
          rw [sq, ← mul_assoc, ← hab, Nat.lt_mul_iff_one_lt_right (by linarith)]
          linarith
        rw [show p + (a * b ^ 2 - p) = a * b^2 by omega, hab]
        ring
      . have : p - 1 ≠ p - a := by omega
        simp [this]
  -- to prove unique solution from primeness, we wil show the solution is (p-1, p^2-p)
  . have hp' : 1 < p := h.one_lt
    have : p < p^2 := by refine lt_self_pow₀ hp' (by norm_num)
    use ⟨p - 1, p^2 - p⟩
    -- by lemma it is a solution
    simp [l_diaphantine_soln_of_one_lt hp']
    -- if there  is another solution then p - a ∣ p^2 so p - a = 1, p, p^2
    rintro a b ha hb h'
    have : p - a ∣ p^2 := by
      rw [← h']
      simp
    obtain ⟨k, hk, hk'⟩ := Nat.dvd_prime_pow h |>.mp this
    interval_cases k
    -- if p - a = 1 this gives our known solutio (a, b) = (p-1, p^2 - p)
    . simp at hk'
      have ha : a = p - 1 := by omega
      simp [ha] at h' ⊢
      rw [show p - (p - 1) = 1 by omega] at h'
      simp at h'
      omega
    -- if p - a = p, this is impossible as then a = 0
    . simp at hk'
      omega
    -- if p - a = p^2, this is also impossible as then p^2 ≤ p
    . have : p ^ 2 ≤ p := by
        trans p - a
        . linarith
        . omega
      linarith