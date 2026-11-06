import Mathlib

-- Let $X$ be an integer greater than or equal to 2. Given $X+1$ positive integers $a_1, a_2, \ldots, a_{X+1}$ such that their sum is $\sum_{i=1}^{X+1} a_i = X^2$. Show that the maximum value of the greatest common divisor of $a_1, a_2, \ldots, a_{X+1}$ is $X^2/K_0$, where $K_0$ is the smallest divisor of $X^2$ such that $K_0 \ge X+1$.
theorem number_theory_641653 (X : ℕ) (hX : 2 ≤ X) :
    IsGreatest {/- Finset.gcd Finset.univ a -/ Finset.univ.gcd a | (a : Fin (X + 1) → ℕ) (_ : ∀ i, 0 < a i) (_ : ∑ i, a i = X ^ 2)}
    (let K₀ := sInf {k | k ∣ X ^ 2 ∧ k ≥ X + 1}; X ^ 2 / K₀) := by
  have : {Finset.univ.gcd a | (a : Fin (X + 1) → ℕ) (_ : ∀ i, 0 < a i) (_ : ∑ i, a i = X ^ 2)} =
      {d₀ | ∃ c : Fin (X + 1) → ℕ, (∀ i, 0 < c i) ∧ (Finset.univ.gcd c = 1) ∧ (d₀ * ∑ i, c i = X ^ 2)} := by
    -- 1. Let $d_0 = \gcd(a_1, \ldots, a_{X+1})$. Then $a_i = d_0 c_i$ for positive integers $c_i$ with $\gcd(c_1, \ldots, c_{X+1})=1$.
    -- 2. The sum $\sum a_i = X^2$ implies $d_0 \sum c_i = X^2$. Let $S_c = \sum c_i$.
    ext d₀
    constructor
    . simp
      intro a sum_a_eq_X_sq a_pos eq_d₀
      let c i := a i / d₀
      use c
      constructor
      . intro i
        simp [c]
        subst eq_d₀
        constructor
        . suffices Finset.univ.gcd a ≠ 0 by
            omega
          intro gcd_eq_0
          have := Finset.gcd_eq_zero_iff.mp gcd_eq_0
          specialize this i (by simp)
          specialize a_pos i
          linarith
        . have : Finset.univ.gcd a ∣ a i :=
            Finset.gcd_dvd (by simp)
          exact Nat.le_of_dvd (a_pos i) this
      . constructor
        . simp [c, ← eq_d₀]
          let i : Fin (X + 1) := 0
          apply Finset.gcd_div_eq_one (f := a) (i := i) (by simp)
          . exact Nat.not_eq_zero_of_lt (a_pos i)
        . convert sum_a_eq_X_sq
          have : ∀ i, a i = d₀ * c i := by
            intro i
            simp [c]
            have : Finset.univ.gcd a ∣ a i :=
              Finset.gcd_dvd (by simp)
            rw [eq_d₀] at this
            exact Eq.symm (Nat.mul_div_cancel' this)
          simp_rw [this]
          rw [Finset.mul_sum]
    . simp
      intro c c_pos gcd_c_eq_1 d₀_mul_sum_c_eq_X_sq
      let a i := d₀ * c i
      use a
      simp [a]
      constructor
      . rw [← Finset.mul_sum]
        exact d₀_mul_sum_c_eq_X_sq
      . constructor
        . intro i
          constructor
          . have : d₀ * ∑ i, c i > 0 := by
              nlinarith
            exact Nat.pos_of_mul_pos_right this
          . exact c_pos i
        . rw [Finset.gcd_mul_left]
          simp
          simp [gcd_c_eq_1]
  rw [this]
  set K₀ := sInf {k | k ∣ X ^ 2 ∧ k ≥ X + 1}
  have K₀_in : K₀ ∈ {k | k ∣ X ^ 2 ∧ k ≥ X + 1} := by
    unfold K₀
    refine Nat.sInf_mem ?_
    have : X ^ 2 ∈ {k | k ∣ X ^ 2 ∧ k ≥ X + 1} := by
      simp
      nlinarith
    exact Set.nonempty_of_mem this
  constructor
  swap
  . simp [upperBounds]
    intro d₀ c c_pos gcd_c_eq_1 d₀_mul_sum_c_eq_X_sq
    -- 3. $d_0 S_c = X^2$. Since $c_i \ge 1$, $S_c \ge X+1$. Also, $S_c$ must be a divisor of $X^2$.
    set S_c := ∑ i, c i
    have S_c_dvd_X_2 : S_c ∣ X ^ 2 := by
      exact Dvd.intro_left d₀ d₀_mul_sum_c_eq_X_sq
    have S_ge_X_plus_1 : S_c ≥ X + 1 := by
      suffices S_c ≥ ∑ i : Fin (X + 1), 1 by
        simp at this
        exact this
      apply Finset.sum_le_sum
      intro i _
      exact c_pos i
    -- 4. To maximize $d_0 = X^2/S_c$, $S_c$ must be minimized. Let $K_0$ be the smallest divisor of $X^2$ such that $K_0 \ge X+1$. This $K_0$ is the minimum possible value for $S_c$.
    have : S_c ≥ K₀ := by
      unfold K₀
      have : S_c ∈ {k | k ∣ X ^ 2 ∧ k ≥ X + 1} := by
        exact Set.mem_sep S_c_dvd_X_2 S_ge_X_plus_1
      exact Nat.sInf_le this
    have : d₀ * K₀ ≤ X ^ 2 := by
      nlinarith
    refine (Nat.le_div_iff_mul_le ?_).mpr this
    . simp at K₀_in
      have := K₀_in.2
      linarith
  . simp
    -- 5. The existence of $K_0$ is guaranteed as $X^2$ itself is a divisor of $X^2$ and $X^2 \ge X+1$ for $X \ge 2$.
    -- 6. The maximum value of $d_0$ is $X^2/K_0$.
    -- 7. This value is achievable by selecting $c_1 = K_0-X$ and $c_i=1$ for $i=2, \ldots, X+1$. These $c_i$ are all $\ge 1$ (since $K_0 \ge X+1 \implies K_0-X \ge 1$), their sum is $K_0$, and their $\gcd$ is 1.
    let c : Fin (X + 1) → ℕ
      | 0 => K₀ - X
      | i => 1
    use c
    have c_0_eq_0 : c 0 = K₀ - X :=
      rfl
    have c_ne_0_eq_1 : ∀ i ≠ 0, c i = 1 := by
      intro i i_ne_0
      simp [c, i_ne_0]
    have K₀_gt_X : K₀ > X := by
      simp at K₀_in
      have := K₀_in.2
      linarith
    constructor
    . intro i
      by_cases w_i_eq_0 : i = 0
      . simp [w_i_eq_0]
        rw [c_0_eq_0]
        omega
      . exact Nat.lt_of_sub_eq_succ (c_ne_0_eq_1 i w_i_eq_0)
    . set univ := (Finset.univ : Finset (Fin (X + 1)))
      constructor
      . have : univ = {0, 1} ∪ (univ \ {0, 1}) := by
          refine Eq.symm (Finset.union_sdiff_of_subset ?_)
          intro i _
          unfold univ
          simp
        rw [this]
        rw [Finset.gcd_union]
        simp
        rw [c_0_eq_0]
        have : c 1 = 1 := c_ne_0_eq_1 1 (by aesop)
        rw [this]
        simp
      . -- 8. Then $a_i = (X^2/K_0)c_i$ are positive integers which sum to $X^2$ and their gcd is $X^2/K_0$.
        set S_c := ∑ i, c i
        have : S_c = K₀ := by
          unfold S_c
          have : univ = {0} ∪ (univ \ {0}) := by
            simp [univ]
          show ∑ i ∈ univ, c i = K₀
          rw [this]
          rw [Finset.sum_union (by simp [univ])]
          simp
          rw [c_0_eq_0]
          have : ∑ i ∈ univ \ {0}, c i = ∑ i ∈ univ \ {0}, 1 := by
            apply Finset.sum_congr rfl
            intro i i_in
            simp at i_in
            rcases i_in with ⟨_, i_ne_0⟩
            exact c_ne_0_eq_1 i i_ne_0
          simp at this
          rw [this]
          have : (univ \ {0}).card = X := by
            rw [Finset.card_sdiff (by simp [univ])]
            simp [univ]
          rw [this]
          omega
        rw [this]
        have : K₀ ∣ X ^ 2 := K₀_in.1
        exact Nat.div_mul_cancel this
