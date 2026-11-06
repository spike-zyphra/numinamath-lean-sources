  import Mathlib

set_option maxHeartbeats 400000

/-
Let $P$ be a prime number. Consider the sum $S(P) = \sum_{i=1}^{P-1} \sum_{j=1}^{P-1} \sum_{k=1}^{P-1}\left\lfloor\frac{i \cdot j \cdot k}{P}\right\rfloor$.
Show that $S(P) = \frac{(P-1)^3(P-2)(P+2)}{8}$.
 -/
theorem number_theory_638487 (P : ℕ) (hP : Nat.Prime P) :
    ∑ i ∈ Finset.Icc 1 (P - 1), ∑ j ∈ Finset.Icc 1 (P - 1), ∑ k ∈ Finset.Icc 1 (P - 1), ((i * j * k) / P : ℕ) =
    (((P - 1)^3 * (P - 2) * (P + 2)) / 8 : ℚ) := by
  let sum_i_j_k := fun (f : ℕ → ℕ → ℕ → ℚ) =>
    ∑ i ∈ Finset.Icc 1 (P - 1), ∑ j ∈ Finset.Icc 1 (P - 1), ∑ k ∈ Finset.Icc 1 (P - 1), f i j k
  have : ∑ i ∈ Finset.Icc 1 (P - 1), ∑ j ∈ Finset.Icc 1 (P - 1), ∑ k ∈ Finset.Icc 1 (P - 1), (i * j * k / P) =
      sum_i_j_k (fun i j k => (i * j * k / P : ℕ)) := by
    unfold sum_i_j_k
    /-
    push_cast
    rfl
     -/
    norm_cast
  rw [this]
  -- 1. Rewrite $\lfloor ijk/P \rfloor$ as $(ijk - (ijk \pmod P))/P$.
  have P_ne_zero := hP.ne_zero
  /-
  have : ∀ i j k , ((i * j * k) / P : ℕ) = ((i * j * k - (i * j * k % P)) / P : ℚ) := by
    intro i j k
    generalize i_j_k_eq : i * j * k = n
   -/
  have div_P_ℕ_eq_sub_mod_div_P_ℚ : ∀ n, (n / P : ℕ) = ((n - (n % P) : ℕ) / P : ℚ) := by
    intro n
    have := Nat.div_add_mod n P
    set div := n / P
    set mod := n % P
    rw [←this]
    field_simp [P_ne_zero]
  simp [div_P_ℕ_eq_sub_mod_div_P_ℚ]
  -- 2. Split the sum into $\frac{1}{P}\sum ijk - \frac{1}{P}\sum (ijk \pmod P)$.
  have : ∀ n, ((n - (n % P) : ℕ) / P : ℚ) = n / P - (n % P : ℕ) / P := by
    intro n
    field_simp [P_ne_zero]
    have : (n - n % P : ℕ) = (n - n % P : ℤ) := by
      have : n ≥ n % P := by
        exact Nat.mod_le n P
      omega
    qify at this
    rw [this]
    rfl
  simp_rw [this]
  have : sum_i_j_k (fun i j k => ((i * j * k : ℕ) / P - (i * j * k % P : ℕ) / P)) =
      sum_i_j_k (fun i j k => (i * j * k : ℕ)) / P - sum_i_j_k (fun i j k => (i * j * k % P : ℕ)) / P := by
    unfold sum_i_j_k
    simp_rw [Finset.sum_sub_distrib]
    simp_rw [Finset.sum_div]
  rw [this]
  -- 3. Evaluate $\sum ijk = (\sum i)^3 = \left(\frac{P(P-1)}{2}\right)^3$. So the first term is $\frac{P^2(P-1)^3}{8}$.
  have sum_icc_id_eq : ∑ i ∈ Finset.Icc 1 (P - 1), i = (P * (P - 1)) / 2 := by
    have := Finset.sum_range_id P
    convert this using 1
    have : Finset.range P = {0} ∪ Finset.Icc 1 (P - 1) := by
      ext i
      simp
      omega
    rw [this]
    have : Disjoint {0} (Finset.Icc 1 (P - 1)) := by
      simp
    rw [Finset.sum_union this]
    simp
  have P_sub_1_to_ℚ : (P - 1 : ℕ) = (P - 1 : ℤ) := by
    omega
  qify at P_sub_1_to_ℚ
  have P_mul_P_sub_1_div_2_to_ℚ : (P * (P - 1) / 2 : ℕ) = (P * (P - 1) / 2 : ℚ) := by
    have : 2 ∣ P * (P - 1) := by
      mod_cases P % 2
      . have : 2 ∣ P := by
          exact Nat.dvd_of_mod_eq_zero H
        exact Dvd.dvd.mul_right this (P - 1)
      . have : 2 ∣ P - 1 := by
          /-
          have : (P - 1) ≡ 0 [MOD 2] := by
            omega
           -/
          change P % 2 = 1 at H
          omega
        exact Dvd.dvd.mul_left this P
    rcases this with ⟨c, P_mul_P_sub_1_eq⟩
    rw [P_mul_P_sub_1_eq]
    qify at P_mul_P_sub_1_eq
    rw [P_sub_1_to_ℚ] at P_mul_P_sub_1_eq
    rw [P_mul_P_sub_1_eq]
    simp
  have : sum_i_j_k (fun i j k => (i * j * k : ℕ)) = ((P * (P - 1)) / 2) ^ 3 := by
    dsimp [sum_i_j_k]
    conv_lhs => norm_cast
    have : ∀ i j k : ℕ, i * j * k = i * (j * k) := by
      intro i j k
      ring
    simp_rw [this]
    simp_rw [←Finset.mul_sum, ←Finset.sum_mul]
    --simp_rw [←Finset.mul_sum, ←Finset.sum_mul]
    have : ∑ j ∈ Finset.Icc 1 (P - 1), ∑ k ∈ Finset.Icc 1 (P - 1), j * k =
        (∑ i ∈ Finset.Icc 1 (P - 1), i) * (∑ i ∈ Finset.Icc 1 (P - 1), i) := by
      --simp_rw [←Finset.mul_sum]
      --simp [←Finset.mul_sum]
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    rw [this]
    rw [sum_icc_id_eq]
    push_cast
    rw [P_mul_P_sub_1_div_2_to_ℚ]
    ring
  rw [this]
  -- 4. Evaluate $\sum (ijk \pmod P)$ by first summing over $k$. For fixed $i,j$, $\{ijk \pmod P\}_{k=1}^{P-1}$ is a permutation of $\{1, \dots, P-1\}$. So $\sum_{k=1}^{P-1} (ijk \pmod P) = \frac{P(P-1)}{2}$.
  -- 5. Sum this result over $i$ and $j$: $(P-1)^2 \frac{P(P-1)}{2} = \frac{P(P-1)^3}{2}$. So the second term is $\frac{(P-1)^3}{2}$.
  have P_pos := hP.pos
  have P_gt_1 := hP.one_lt
  have : sum_i_j_k (fun i j k => (i * j * k % P : ℕ)) = (P * (P - 1) ^ 3) / 2 := by
    unfold sum_i_j_k
    have : ∀ n, ¬ P ∣ n → ∑ i ∈ Finset.Icc 1 (P - 1), n * i % P = ∑ i ∈ Finset.Icc 1 (P - 1), i := by
      intro n not_P_dvd_n
      set s := Finset.Icc 1 (P - 1)
      set f := (n * . % P)
      have s_image_f_eq_s : s.image f = s := by
        simp [s, f]
        --hint
        ext x
        simp
        constructor
        . simp
          intro y y_ge y_le n_mul_y_mod_P_eq_x
          constructor
          . suffices x ≠ 0 by
              omega
            subst n_mul_y_mod_P_eq_x
            suffices ¬ P ∣ n * y by
              omega
            have : ¬ P ∣ y := by
              intro P_dvd_y
              have : y ≥ P := by
                exact Nat.le_of_dvd y_ge P_dvd_y
              omega
            exact Nat.Prime.not_dvd_mul hP not_P_dvd_n this
          . have : x < P := by
              rw [←n_mul_y_mod_P_eq_x]
              exact Nat.mod_lt _ P_pos
            omega
        . simp
          intro x_ge x_le
          have : n.Coprime P := by
            suffices P.Coprime n by
              exact Nat.coprime_comm.mp this
            exact (Nat.Prime.coprime_iff_not_dvd hP).mpr not_P_dvd_n
          have := Nat.exists_mul_emod_eq_one_of_coprime this P_gt_1
          rcases this with ⟨m, n_m_mod_P_eq_1⟩
          use m * x % P
          have x_lt_P : x < P := by
            omega
          constructor
          . constructor
            . /-
              suffices m * x % P ≠ 0 by
                omega
               -/
              suffices ¬ P ∣ m * x by
                omega
              have not_dvd_m : ¬ P ∣ m := by
                intro P_dvd_m
                have : P ∣ n * m := by
                  exact Dvd.dvd.mul_left P_dvd_m n
                have : n * m % P = 0 := by
                  omega
                linarith
              have not_dvd_x : ¬ P ∣ x := by
                exact Nat.not_dvd_of_pos_of_lt x_ge x_lt_P
              exact Nat.Prime.not_dvd_mul hP not_dvd_m not_dvd_x
            . have : m * x % P < P := by
                exact Nat.mod_lt (m * x) P_pos
              omega
          . suffices mod_eq : n * (m * x % P) ≡ x [MOD P] by
              have : x = x % P := by
                exact Eq.symm (Nat.mod_eq_of_lt x_lt_P)
              conv_rhs => rw [this]
              exact mod_eq
            calc
              n * (m * x % P) ≡ n * (m * x) [MOD P] := by
                gcongr
                . unfold Nat.ModEq
                  simp
              _ = (n * m) * x := by
                ring
              _ ≡ 1 * x [MOD P] := by
                gcongr
                . unfold Nat.ModEq
                  convert n_m_mod_P_eq_1
                  . exact Nat.mod_eq_of_lt P_gt_1
              _ = x := by simp
      --have : Set.InjOn (n * . % P) s := by
      have : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y := by
        simp [s, f]
        intro x _ _ y _ _ mod
        zify at mod
        /-
        have : ((n * x - n * y) % P : ℤ) = 0 := by
          omega
        -/
        change n * x ≡ n * y [ZMOD P] at mod
        have : n * (x - y) ≡ 0 [ZMOD P] := by
          calc
            (n * (x - y) : ℤ) = n * x - n * y := by ring
            _ ≡ n * x - n * x [ZMOD P] := by gcongr
            _ = 0 := by simp
        have : (P : ℤ) ∣ n * (x - y) := by
          exact Int.dvd_of_emod_eq_zero this
        --zify at not_P_dvd_n
        have P_dvd_diff_natAbs := Int.Prime.dvd_mul hP this
        simp at this
        simp [not_P_dvd_n] at P_dvd_diff_natAbs
        have : (x - y : ℤ).natAbs < P := by
          omega
        have : (x - y : ℤ).natAbs = 0 := by
          exact Nat.eq_zero_of_dvd_of_lt P_dvd_diff_natAbs this
        omega
      have := Finset.sum_image (f := id) (s := s) (g := f) this
      simp at this
      rw [←this]
      rw [s_image_f_eq_s]
    have : ∑ i ∈ Finset.Icc 1 (P - 1),
        ∑ j ∈ Finset.Icc 1 (P - 1),
        ∑ k ∈ Finset.Icc 1 (P - 1),
        (fun i j k ↦ (i * j * k % P)) i j k =
        ∑ i ∈ Finset.Icc 1 (P - 1),
        ∑ j ∈ Finset.Icc 1 (P - 1),
        ∑ k ∈ Finset.Icc 1 (P - 1),
        k := by
      apply Finset.sum_congr rfl
      intro i i_in
      apply Finset.sum_congr rfl
      intro j j_in
      apply this (i * j)
      simp at i_in j_in
      intro P_dvd_i_j
      have : P ∣ i ∨ P ∣ j := by
        exact (Nat.Prime.dvd_mul hP).mp P_dvd_i_j
      rcases this with P_dvd_i | P_dvd_j
      . have : i > 0 := by
          linarith
        have : P ≤ i := by
          exact Nat.le_of_dvd this P_dvd_i
        omega
      . have : j > 0 := by
          linarith
        have : P ≤ j := by
          exact Nat.le_of_dvd this P_dvd_j
        omega
    conv_lhs => norm_cast
    rw [this]
    rw [sum_icc_id_eq]
    simp
    rw [P_sub_1_to_ℚ, P_mul_P_sub_1_div_2_to_ℚ]
    ring
  rw [this]
  -- 6. Combine to get $S(P) = \frac{P^2(P-1)^3}{8} - \frac{(P-1)^3}{2} = \frac{(P-1)^3(P^2-4)}{8}$.
  -- 7. Factor $P^2-4$ to obtain the final expression $S(P) = \frac{(P-1)^3(P-2)(P+2)}{8}$.
  field_simp [this]
  ring
