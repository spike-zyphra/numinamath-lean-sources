import Mathlib

open Set Polynomial

/- x ^ 3 - 3 x + 1 is continuous. -/
lemma continuous_f {f : ℝ → ℝ} (hf : f = fun x => x ^ 3 - 3 * x ^ 2 + 1) {s : Set ℝ} : ContinuousOn f s := by
  rw [hf]
  apply Continuous.continuousOn
  continuity

/- By the intermediate value theorem, there exists a root of f at [-11/20, 1 / 3]. -/
lemma roots_of_equation₁ {f : ℝ → ℝ} (hf : f = fun x => x ^ 3 - 3 * x ^ 2 + 1) : ∃ α : ℝ, α ∈ Icc (-11 / 20) (1 / 3) ∧ f α = 0 := by
  have h₁ : (-11 / 20 : ℝ) ∈ Icc (-11 / 20) (1 / 3) := by simp; norm_num
  have h₂ : (1 / 3 : ℝ) ∈ Icc (-11 / 20) (1 / 3) := by simp; norm_num
  have h₃ : IsPreconnected (Icc (-11 / 20) (1 / 3) : Set ℝ) := by exact isPreconnected_Icc
  obtain h := IsPreconnected.intermediate_value h₃ h₁ h₂ (f := f) (continuous_f hf)
  have h_mem : 0 ∈ Icc (f (-11 / 20)) (f (1 / 3)) := by
    simp [hf]
    norm_num
  apply h at h_mem
  obtain ⟨α, hα_mem, hα_eq⟩ := h_mem
  use α, hα_mem

/- By the intermediate value theorem, there exists a root of f at [3/5, 2/3]. -/
lemma roots_of_equation₂ {f : ℝ → ℝ} (hf : f = fun x => x ^ 3 - 3 * x ^ 2 + 1) : ∃ α : ℝ, α ∈ Icc (3 / 5) (2 / 3) ∧ f α = 0 := by
  have h₁ : (3 / 5 : ℝ) ∈ Icc (3 / 5) (2 / 3) := by simp; norm_num
  have h₂ : (2 / 3 : ℝ) ∈ Icc (3 / 5) (2 / 3) := by simp; norm_num
  have h₃ : IsPreconnected (Icc (3 / 5) (2 / 3) : Set ℝ) := by exact isPreconnected_Icc
  obtain h := IsPreconnected.intermediate_value h₃ h₂ h₁ (f := f) (continuous_f hf)
  have h_mem : 0 ∈ Icc (f (2 / 3)) (f (3 / 5)) := by
    simp [hf]
    norm_num
  apply h at h_mem
  obtain ⟨α, hα_mem, hα_eq⟩ := h_mem
  use α, hα_mem

/- By the intermediate value theorem, there exists a root of f at [2, 3]. -/
lemma roots_of_equation₃ {f : ℝ → ℝ} (hf : f = fun x => x ^ 3 - 3 * x ^ 2 + 1) : ∃ α : ℝ, α ∈ Icc 2 3 ∧ f α = 0 := by
  have h₁ : (2: ℝ) ∈ Icc 2 3 := by simp; norm_num
  have h₂ : (3 : ℝ) ∈ Icc 2 3 := by simp; norm_num
  have h₃ : IsPreconnected (Icc 2 3 : Set ℝ) := by exact isPreconnected_Icc
  obtain h := IsPreconnected.intermediate_value h₃ h₁ h₂ (f := f) (continuous_f hf)
  have h_mem : 0 ∈ Icc (f 2) (f 3) := by
    simp [hf]
    norm_num
  apply h at h_mem
  obtain ⟨α, hα_mem, hα_eq⟩ := h_mem
  use α, hα_mem

/- The roots of f are exactly α, β, γ such that α β γ = -1, α + β + γ = 3 and α * β + β * γ + γ * α = 0.  -/
lemma roots_of_equation {f : ℝ → ℝ} (hf : f = fun x => x ^ 3 - 3 * x ^ 2 + 1) : ∃ α β γ, α ∈ Icc (-11 / 20) (1 / 3) ∧ β ∈ Icc (3 / 5) (2 / 3) ∧ γ ∈ Icc 2 3 ∧
    α * β * γ = -1 ∧ α + β + γ = 3 ∧ α * β + β * γ + γ * α = 0 ∧
    ∀ x, f x = (x - α) * (x - β) * (x - γ) := by
  -- The algebraic equation $x^{3}-3 x^{2}+1=0$ admits three real roots $\alpha, \beta, \gamma$.
  obtain ⟨α, hα_mem, hα_eq⟩ := roots_of_equation₁ hf
  obtain ⟨β, hβ_mem, hβ_eq⟩ := roots_of_equation₂ hf
  obtain ⟨γ, hγ_mem, hγ_eq⟩ := roots_of_equation₃ hf
  use α, β, γ, hα_mem, hβ_mem, hγ_mem
  let P : ℝ[X] := X ^ 3 - 3 * X ^ 2 + 1
  -- The polynomial $P$ has degree 3, is monic, and has roots $\alpha, \beta, \gamma$.
  have hP : P.natDegree = 3 := by
    have : (X ^ 3 - 3 * X ^ 2 : ℝ[X]).natDegree = 3 := by
      rw [natDegree_sub_eq_left_of_natDegree_lt]
      all_goals simp
    rw [natDegree_add_eq_left_of_natDegree_lt]
    all_goals simp [this]
  have hP_ne : P ≠ 0 := by intro h; simp [h] at hP
  -- Hence, $P$ has exactly three distinct roots.
  have h_roots : P.roots = {α, β, γ} := by
    symm
    refine Multiset.eq_of_le_of_card_le ?_ ?_
    · refine (Multiset.le_iff_subset ?_).mpr ?_
      · refine Multiset.toFinset_card_eq_card_iff_nodup.mp ?_
        simp
        apply Finset.card_eq_three.mpr
        have h₁ : α < β := by
          apply lt_of_le_of_lt hα_mem.2
          apply lt_of_lt_of_le ?_ hβ_mem.1
          norm_num
        have h₂ : β < γ := by
          apply lt_of_le_of_lt hβ_mem.2
          apply lt_of_lt_of_le ?_ hγ_mem.1
          norm_num
        use α, β, γ
        split_ands
        · apply ne_of_lt h₁
        · apply ne_of_lt (lt_trans h₁ h₂)
        · apply ne_of_lt h₂
        · rfl
      · intro x hx
        simp [hP_ne, P] at hx ⊢
        rcases hx with hx | hx | hx <;> rw [hx]
        · simpa [hf] using hα_eq
        · simpa [hf] using hβ_eq
        · simpa [hf] using hγ_eq
    · simp [←hP]
      exact card_roots' P
  have hP_monic : P.Monic := by
    refine Monic.def.mpr ?_
    unfold Polynomial.leadingCoeff
    simp [hP, P]
    obtain h := coeff_C (R := ℝ) (a := 1) (n := 3)
    simp at h
    simp [h]
  have hsplit : Splits (RingHom.id ℝ) P := by
    refine splits_iff_card_roots.mpr ?_
    simp [hP, h_roots]
  -- Therefore, f = (X - α) * (X - β) * (X - γ).
  obtain h := Polynomial.eq_prod_roots_of_monic_of_splits_id hP_monic hsplit
  simp [h_roots] at h
  -- The roots of $P$ satisfy Vieta's formulas.
  have hcoeff_0 : α * β * γ = -1 := by
    apply congrArg (fun P => P.coeff 0) at h
    ring_nf at h
    simp [P] at h
    simp [h]
  have hcoeff_1 : α * β + β * γ + γ * α = 0 := by
    apply congrArg (fun P => P.coeff 1) at h
    ring_nf at h
    simp [P] at h
    obtain hc := coeff_C (R := ℝ) (a := 1) (n := 1)
    simp at hc
    simp [←hc, h]
    simp [coeff_C]
    ring
  have hcoeff_2 : α + β + γ = 3 := by
    apply congrArg (fun P => P.coeff 2) at h
    ring_nf at h
    simp [P] at h
    have : (X : ℝ[X]).coeff 2 = 0 := by rw [coeff_X]; simp
    simp [this] at h
    have hc := coeff_C (R := ℝ) (a := 1) (n := 2)
    simp at hc
    simp [hc, coeff_C] at h
    linear_combination h
  simp [hcoeff_0, hcoeff_1, hcoeff_2]
  intro x
  apply congrArg (fun P => P.eval x) at h
  simp [P] at h
  simp [hf, h, mul_assoc]

/- 7.
(FRA 2) Let $a$ be the greatest positive root of the equation $x^{3}-3 x^{2}+1=$ 0 .
Show that $\left[a^{1788}\right]$ and $\left[a^{1988}\right]$ are both divisible by 17 .
( $[x]$ denotes the integer part of $x$.) -/
theorem number_theory_24177 {a : ℝ} (ha : IsGreatest {x : ℝ | x > 0 ∧ x^3 - 3 * x^2 + 1 = 0 } a) :
    17 ∣ ⌊a^(1788)⌋ ∧ 17 ∣ ⌊a^(1988)⌋ := by
  obtain ⟨⟨ha_pos, ha_eq⟩, ha⟩ := ha
  set f : ℝ → ℝ := fun x => x ^ 3 - 3 * x ^ 2 + 1 with hf
  -- The algebraic equation $x^{3}-3 x^{2}+1=0$ admits three real roots $α, β, γ$
  obtain ⟨α, β, γ, hα, hβ, hγ, h₃, h₁, h₂, hf_apply⟩ := roots_of_equation hf
  have hα_eq : f α = 0 := by simp [hf_apply]
  have hβ_eq : f β = 0 := by simp [hf_apply]
  have hγ_eq : f γ = 0 := by simp [hf_apply]
  -- We have $α < β < γ$.
  have hαβ : α < β := by
    apply lt_of_le_of_lt hα.2
    apply lt_of_lt_of_le ?_ hβ.1
    norm_num
  have hβγ : β < γ := by
    apply lt_of_le_of_lt hβ.2
    apply lt_of_lt_of_le ?_ hγ.1
    norm_num
  -- Therefore, a = γ.
  have ha_eq_γ : a = γ := by
    obtain h := hf_apply a
    simp [hf, ha_eq] at h
    have hγ_mem : γ ∈ {x | x > 0 ∧ x ^ 3 - 3 * x ^ 2 + 1 = 0} := by
      constructor
      · apply lt_of_lt_of_le ?_ hγ.1
        norm_num
      · simpa [hf] using hγ_eq
    have h_ge := ha hγ_mem
    rcases h with (h | h) | h
    · have : a - α ≠ 0 := by
        apply ne_of_gt
        simp
        apply lt_of_lt_of_le (lt_trans hαβ hβγ) h_ge
      contradiction
    · have : a - β ≠ 0 := by
        apply ne_of_gt
        simp
        apply lt_of_lt_of_le hβγ h_ge
      contradiction
    · apply sub_eq_zero.mp h
  rw [ha_eq_γ]
  -- $$ Define, for all naturals $n$, u_n = α ^ n + β ^ n + γ ^ n.
  let u : ℕ → ℝ := fun n => α ^ n + β ^ n + γ ^ n
  -- $$ It holds that $u_{n+3}=3 u_{n+2}-u_{n}$.
  have hu_succ : ∀ n : ℕ, u (n + 3) = 3 * u (n + 2) - u n := by
    intro n
    simp [u]
    apply sub_eq_zero.mp
    trans α ^ n * f α + β ^ n * f β + γ ^ n * f γ
    · simp [hf]; ring
    · simp [hα_eq, hβ_eq, hγ_eq]
  -- Also, $u_n$ is an integer for $n=0,1,2$ as can be determined using Vieta’s formulas.
  -- α ^ 0 + β ^ 0 + γ ^ 0 = 3
  have hu0 : u 0 = 3 := by simp [u]; norm_num
  -- α ^ 1 + β ^ 1 + γ ^ 1 = 3
  have hu1 : u 1 = 3 := by
    simp [u, h₁]
  -- α ^ 2 + β ^ 2 + γ ^ 2 = 9
  have hu2 : u 2 = 9 := by
    simp [u]
    trans (α + β + γ) ^ 2 - 2 * (α * β + β * γ + γ * α)
    · ring
    · simp [h₁, h₂]; ring
  -- Thus, $u_n$ is an integer for all $n$.
  have hu_int : ∀ n, ∃ a : ℤ, u n = a := by
    intro n
    induction n using Nat.strong_induction_on
    rename_i n ih
    by_cases hn : n ≤ 2
    · interval_cases n
      · use 3; simp [hu0]
      · use 3; simp [hu1]
      · use 9; simp [hu2]
    · simp at hn
      have : n - 3 + 2 = n - 1 := by
        apply Nat.eq_sub_of_add_eq
        simp [add_assoc]
        rw [Nat.sub_add_cancel hn]
      obtain ⟨a, iha⟩ := ih (n - 3 + 2) (by rw [this]; exact Nat.sub_one_lt_of_lt hn)
      obtain ⟨c, ihc⟩ := ih (n - 3) (by refine Nat.sub_lt ?_ ?_; exact Nat.zero_lt_of_lt hn; simp)
      use 3 * a - c
      simp [←iha, ←ihc, ←hu_succ]
      congr
      rw [Nat.sub_add_cancel hn]
  obtain ⟨u_int, hu_int⟩ : ∃ u_int : ℕ → ℤ, ∀ n, u_int n = u n := by
    use fun n => Classical.choose (hu_int n)
    intro n
    simp
    symm
    apply Classical.choose_spec (hu_int n)
  -- We also have $u_int 0 = 3$, $u_int 1 = 3$, $u_int 2 = 9$.
  -- and $u_{n+3}=3 u_{n+2}-u_{n}$.
  have hu_int0 : u_int 0 = 3 := by apply Int.cast_inj (α := ℝ) |>.mp; rw [hu_int]; simp [hu0]
  have hu_int1 : u_int 1 = 3 := by apply Int.cast_inj (α := ℝ) |>.mp; rw [hu_int]; simp [hu1]
  have hu_int2 : u_int 2 = 9 := by apply Int.cast_inj (α := ℝ) |>.mp; rw [hu_int]; simp [hu2]
  have hu_int_succ : ∀ n, u_int (n + 3) = 3 * u_int (n + 2) - u_int n := by
    intro n
    apply Int.cast_inj (α := ℝ) |>.mp
    simp [hu_int, hu_succ]
  -- Obviously, $0 < α^{n}+β^{n} < 1$ for all $n \geq 2$,
  have hpow : ∀ n ≥ (2 : ℕ), α ^ n + β ^ n ∈ Ioo 0 1 := by
    intro n hn
    simp
    constructor
    · apply lt_of_lt_of_le (b := β ^ n + (- |α ^ n|))
      · simp
        gcongr
        apply lt_of_le_of_lt (b := 11 / 20)
        · simp [abs]
          constructor
          · apply le_trans hα.2; norm_num
          · rw [neg_le]
            apply le_trans ?_ hα.1; norm_num
        · apply lt_of_lt_of_le (by norm_num) hβ.1
      · rw [add_comm]
        gcongr
        exact neg_abs_le (α ^ n)
    · apply lt_of_le_of_lt (b := |α ^ n| + β ^ n)
      · gcongr
        exact le_abs_self (α ^ n)
      · simp
        apply lt_of_le_of_lt (b := (11 / 20) ^ 2 + (2 / 3) ^ 2)
        · trans |α| ^ 2 + β ^ 2
          · apply add_le_add
            · apply pow_le_pow_of_le_one
              · simp
              · simp [abs]
                constructor
                · apply le_trans hα.2; norm_num
                · rw [neg_le]
                  apply le_trans ?_ hα.1; norm_num
              · exact hn
            · apply pow_le_pow_of_le_one
              · apply le_trans ?_ hβ.1; norm_num
              · apply le_trans hβ.2; norm_num
              · exact hn
          · gcongr
            · simp [abs]
              constructor
              · apply le_trans hα.2; norm_num
              · rw [neg_le]
                apply le_trans ?_ hα.1; norm_num
            · apply le_trans ?_ hβ.1; norm_num
            · apply le_trans hβ.2; norm_num
        · norm_num
  -- and we see that $u_{n}-1=\left[γ^{n}\right]$ for $n \geq 2$.
  have hfloor_γ : ∀ n ≥ (2 : ℕ), Int.floor (γ ^ n) = u_int n - 1 := by
    intro n hn
    apply Int.floor_eq_iff.mpr
    constructor
    · simp [hu_int, u]
      apply sub_nonneg.mp
      ring_nf
      trans 1 + (-1)
      · simp
      · gcongr
        simp
        apply le_of_lt (hpow n hn).2
    · simp [hu_int, u]
      exact (hpow n hn).1
  -- It is now a question whether $u_{1788}-1$ and $u_{1988}-1$ are divisible by 17 .
  rw [hfloor_γ 1788 (by linarith), hfloor_γ 1988 (by linarith)]
  -- Working modulo 17 ,
  have mod_17 {n : ℕ} : (u_int n) % 17 = (u_int (n % 16)) % 17 := by
    have hu_int_succ_4 {n : ℕ} : u_int (n + 16) = u_int (2 + n) * 2938977 -(u_int n * 1020696) - u_int (1 + n) * 354484 := by
      simp [hu_int_succ]
      ring_nf
    -- $u_{n}$ is periodic modulo 17 , with period 16. 
    have hu_int_succ_4_mod {n : ℕ} : (u_int (n + 16)) % 17 = u_int n % 17 := by
      rw [hu_int_succ_4]
      rw [Int.sub_emod, Int.sub_emod (u_int (2 + n) * 2938977), Int.mul_emod, Int.mul_emod _ 1020696, Int.mul_emod _ 354484]
      simp
      nth_rw 2 [←Int.emod_emod (u_int n), ←Int.emod_emod (u_int n)]
      symm
      apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
      rw [sub_neg_eq_add, ←Int.add_emod]
      nth_rw 1 [←mul_one (a := u_int n % 17), ←mul_add]
      simp

    set k := n / 16
    have hn : n = k * 16 + (n % 16) := by exact Eq.symm (Nat.div_add_mod' n 16)
    clear_value k
    nth_rw 1 [hn]
    clear hn
    induction k with
    | zero => simp
    | succ k ih =>
      trans (u_int ((k * 16 + n % 16) +16)) % 17
      · congr 2
        ring
      · rw [hu_int_succ_4_mod, ih]
  -- Since $1788=16 \cdot 111+12,1988=16 \cdot 124+4$, it follows that $u_{1788} \equiv u_{12} \equiv 1$ and $u_{1988} \equiv u_{4}=1$. 
  -- So, $\left[a^{1788}\right]$ and $\left[a^{1988}\right]$ are divisible by 17 .
  constructor
  all_goals
    apply Int.dvd_sub_of_emod_eq; simp [mod_17]
    simp [hu_int_succ, hu_int2, hu_int1, hu_int0]
