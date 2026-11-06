import Mathlib

set_option linter.dupNamespace false

namespace number_theory_604468

-- copied and adapted from `PNat`
def NatGt2 := { n : ℕ // 2 < n } deriving DecidableEq

notation "ℕ>2" => NatGt2

def NatGt2.val : ℕ>2 → ℕ := Subtype.val

instance coeNatGt2Nat : Coe ℕ>2 ℕ :=
  ⟨NatGt2.val⟩

-- This doesn't work.
--instance instOfNatNatGt2 n (n_gt_2 : n > 2) : OfNat ℕ>2 n where
instance instOfNatNatGt2 n : OfNat ℕ>2 (n + 3) where
  ofNat := ⟨n + 3, by linarith⟩

-- I tried putting `> 2` into `Condition` and just use `ℕ` but couldn't get it to work.
def Condition (a b : ℕ>2) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∃ n : ℕ → ℕ,
    (∀ i < k, 0 < n i) ∧
    n 0 = a ∧ n (k - 1) = b ∧
    ∀ i < k - 1, (n i + n (i + 1)) ∣ n i * n (i + 1)

-- We write $a \Leftrightarrow b$ if the required sequence exists.
infixl:100 " ⇔ " => Condition

-- It is clear that $\Leftrightarrow$ is an equivalence relation, i.e., $a \Leftrightarrow a$, $(a \Leftrightarrow b$ implies $b \Leftrightarrow a)$, and $(a \Leftrightarrow b, b \Leftrightarrow c$ imply $a \Leftrightarrow c$).
instance isEquivCondition : IsEquiv ℕ>2 Condition where
  refl a := by {
    rcases a with ⟨a, a_gt_2⟩
    unfold Condition
    use 1
    constructor
    simp
    use (fun _ => a)
    constructor
    intro i _
    linarith
    constructor
    rfl
    constructor
    rfl
    intro i hi
    rcases hi
  }
  trans a b c a_equiv_b b_equiv_c := by {
    rcases a_equiv_b with ⟨k₁, k₁_pos, n₁, n₁_pos, n₁_0, n₁_k₁_m_1, n₁_dvd⟩
    rcases b_equiv_c with ⟨k₂, k₂_pos, n₂, n₂_pos, n₂_0, n₂_k₂_m_1, n₂_dvd⟩
    unfold Condition
    let k := k₁ + k₂ - 1
    use k
    constructor
    bound
    --let ℕ.i₂ i := i - k₁ + 1
    --let n i := if i < k₁ then n₁ i else n₂ (i - k₁ + 1)
    --use fun i => if i < k then if i < k₁ then n₁ i else n₂ (i - k₁ + 1) else 0
    use fun i => if i < k₁ then n₁ i else n₂ (i - k₁ + 1)
    constructor
    . intro i _
      split
      . exact n₁_pos i (by assumption)
      . exact n₂_pos (i - k₁ + 1) (by omega) -- `linarith` and `bound` don't work here
    . constructor
      bound
      have : n₁ (k₁ - 1) = n₂ 0 := n₁_k₁_m_1.trans (symm n₂_0)
      constructor
      split
      . have : k₂ = 1 := by omega
        have : k = k₁ := by omega
        calc
          n₁ (k - 1) = n₁ (k₁ - 1) := by congr
          _ = n₂ 0 := by assumption
          _ = n₂ (k₂ - 1) := by congr 1; bound
          _ = c.val := n₂_k₂_m_1
      . have : k - 1 - k₁ + 1 = k₂ - 1 := by omega
        rw [this]
        exact n₂_k₂_m_1
      intro i _

      if i < k₁ - 1 then
        simp [show i < k₁ by omega, show i + 1 < k₁ by omega]
        apply n₁_dvd
        assumption
      /- This actually complicates the proof.
      else
        let i₂ := i + 1 - k₁ -- `i - k₁ + 1` does not work here because when `i = k₁ - 1`, `i - k₁ + 1 = (k₁ - 1) - k₁ + 1 = 0 + 1 = 1`.
        suffices n₂ i₂ + n₂ (i₂ + 1) ∣ n₂ i₂ * n₂ (i₂ + 1) by sorry
        sorry
       -/
      else if i = k₁ - 1 then
        have i_eq : i = k₁ - 1 := by assumption
        simp [show i < k₁ by omega]
        simp [show  ¬ i + 1 < k₁ by omega]
        rw [show n₁ i = n₂ 0 by rw [i_eq]; assumption]
        rw [show i + 1 - k₁ + 1 = 1 by omega]
        exact n₂_dvd 0 (by omega)
      else
        have : ¬ i < k₁ := by omega
        simp [this]
        have : ¬ i + 1 < k₁ := by omega
        simp [this]
        let i₂ := i - k₁ + 1
        rw [show i + 1 - k₁ + 1 = i₂ + 1 by omega]
        exact n₂_dvd i₂ (by omega)
  }
  symm a b a_equiv_b := by {
    rcases a_equiv_b with ⟨k, k_pos, n, n_pos, n_0, n_k_m_1, n_dvd⟩
    unfold Condition
    use k
    constructor
    . exact k_pos
    . use fun i => n (k - 1 - i)
      constructor
      . intro i _
        exact n_pos (k - 1 - i) (by omega)
      . constructor
        . exact n_k_m_1
        . constructor
          . simp
            exact n_0
          . intro i _
            let i' := k - 1 - (i + 1)
            --rw [(rfl : k - 1 - (i + 1) = i')] -- no need
            rw [show k - 1 - i = i' + 1 by omega]
            change n (i' + 1) + n i' ∣ n (i' + 1) * n i'
            rw [show n (i' + 1) + n i' = n i' + n (i' + 1) by ring, show n (i' + 1) * n i' = n i' * n (i' + 1) by ring]
            exact n_dvd i' (by omega)
  }

/- Let $a$ and $b$ be positive integers bigger than 2. Prove that there exists a positive integer $k$ and a sequence $n_{1}, n_{2}, \ldots, n_{k}$ consisting of positive integers, such that $n_{1}=a$, $n_{k}=b$, and $\left(n_{i}+n_{i+1}\right) \mid n_{i} n_{i+1}$ for all $i=1,2, \ldots, k-1$. -/
theorem number_theory_604468 (a b : ℕ>2) : Condition a b := by {
  -- We shall prove that for every $a \geq 3$, ($a$ an integer), $a \Leftrightarrow 3$.
  have equiv_3 : ∀ a : ℕ>2, a ⇔ 3 := by {
    /-
    If $a=2^{s} t$, where $t&gt;1$ is an odd number, we take the sequence

    $$ 2^{s} t, 2^{s}\left(t^{2}-t\right), 2^{s}\left(t^{2}+t\right), 2^{s}(t+1)=2^{s+1} \cdot \frac{t+1}{2} $$
    -/
    have _2_pow_s_mul_t_equiv_2_pow_s_add_1_mul s t (t_odd : t % 2 = 1) (t_gt_1 : t > 1) left_gt_2 :
        ∃ right_gt_2, ⟨2 ^ s * t, left_gt_2⟩ ⇔ ⟨2 ^ (s + 1) * ((t + 1) / 2), right_gt_2⟩ := by {
      have ⟨t', t_add_1_eq⟩ : 2 ∣ t + 1 := by omega
      have t_add_1_div_2_eq : (t + 1) / 2 = t' := by omega
      --let t'' := t' - 1
      --have t_add_1_div_2_eq : (t + 1) / 2 = t'' + 1 := by omega
      rw [t_add_1_div_2_eq]
      --have t_eq : t = 2 * t'' + 1 := by omega
      --subst this
      have right_gt_2 : 2 ^ (s + 1) * t' > 2 := by
        ring_nf
        nlinarith
      use right_gt_2
      unfold Condition
      use 4
      constructor
      . simp
      . let n
        | 0 => 2 ^ s * t
        | 1 => 2 ^ s * t * (t - 1) -- easier to prove than `2 ^ s * (t ^ 2 - t)`
        | 2 => 2 ^ s * t * (t + 1) --2 ^ s * (t ^ 2 + t)
        | 3 => 2 ^ s * (t + 1) --2 ^ (s + 1) * t' --2 ^ (s + 1) * ((t + 1) / 2)
        | n' + 4 => 0
        use n
        unfold n
        constructor
        . intro i _
          have : t - 1 > 0 := by omega
          split <;> nlinarith
        . constructor
          . rfl
          . constructor
            . norm_num
              rw [t_add_1_eq]
              unfold NatGt2.val
              ring
            . intro i _
              /-
              let t_sub_1 := t - 1
              have t_eq_t_sub_1_add_1 : t = t_sub_1 + 1 := by omega
              -/
              have t_sub_1_n_eq_t_sub_q_z : ((t - 1 : ℕ) : ℤ) = (t - 1 : ℤ) := by omega
              split
              . have : 2 ^ s * t + 2 ^ s * t * (t - 1) = 2 ^ s * t ^ 2 := by
                  zify
                  rw [t_sub_1_n_eq_t_sub_q_z]
                  ring
                rw [this]
                ring_nf
                use 2 ^ s * (t - 1)
                ring
              . have : 2 ^ s * t * (t - 1) + 2 ^ s * t * (t + 1) = 2 ^ (s + 1) * t ^ 2 := by
                  zify
                  rw [t_sub_1_n_eq_t_sub_q_z]
                  ring
                rw [this]
                have : 2 ^ s * t * (t - 1) * (2 ^ s * t * (t + 1)) = 2 ^ (2 * s + 1) * t ^ 2 * (t - 1) * t' := by
                  rw [t_add_1_eq]
                  ring
                rw [this]
                use 2 ^ s * (t - 1) * t'
                ring
              . have : 2 ^ s * t * (t + 1) + 2 ^ s * (t + 1) = 2 ^ s * (t + 1) ^ 2 := by ring
                rw [this]
                use 2 ^ s * t
                ring
              . contradiction
              . contradiction
    }
    have a_equiv_2_pow_s a : ∃ s _2_pow_s_gt_2, a ⇔ ⟨2 ^ s, _2_pow_s_gt_2⟩ := by {
      replace ⟨a, a_gt_2⟩ := a
      have exists_eq_2_pow_mul_and_not_dvd {n : ℕ} (hn : n ≠ 0):
          ∃ e n' : ℕ, ¬2 ∣ n' ∧ n = 2 ^ e * n' :=
        Nat.exists_eq_pow_mul_and_not_dvd hn 2 (by simp)
      have eq_2_pow_s_mul_t : ∃ s t, ¬ 2 ∣ t ∧ a = 2 ^ s * t :=
        exists_eq_2_pow_mul_and_not_dvd (by linarith)
      rcases eq_2_pow_s_mul_t with ⟨s, t, neg_2_dvd_t, a_eq_2_pow_s_mul_t⟩
      have : t ≥ 1 := by omega
      -- recursively
      let rec _2_pow_s_mul_t_equiv_2_pow_s' s t left_gt_2 (t_odd : t % 2 = 1) : ∃ s' _2_pow_s'_gt_2, ⟨2 ^ s * t, left_gt_2⟩ ⇔ ⟨2 ^ s', _2_pow_s'_gt_2⟩ := by
        by_cases whether_t_eq_1 : t = 1
        . use s
          subst whether_t_eq_1
          norm_num at left_gt_2
          use left_gt_2
          norm_num
          -- This doesn't work: `exact refl ⟨2 ^ s, left_gt_2⟩`
          exact isEquivCondition.refl ⟨2 ^ s, left_gt_2⟩
        . have mid_gt_2_and_2_pow_s_mul_t_equiv_mid := _2_pow_s_mul_t_equiv_2_pow_s_add_1_mul s t t_odd (by omega) left_gt_2
          rcases exists_eq_2_pow_mul_and_not_dvd (n := (t + 1) / 2) (by omega)
            with ⟨e, t', _, half_t_add_one_eq_2_pow_e_mul_t'⟩
          have t'_odd : t' % 2 = 1 := by omega
          let s' := s + 1 + e
          have mid_eq : 2 ^ (s + 1) * ((t + 1) / 2) = 2 ^ s' * t' := by
            rw [half_t_add_one_eq_2_pow_e_mul_t']
            ring
          --rw [mid_eq] at mid_gt_2, _2_pow_s_mul_t_equiv_mid -- This doesn't work.
          rw [mid_eq] at mid_gt_2_and_2_pow_s_mul_t_equiv_mid
          rcases mid_gt_2_and_2_pow_s_mul_t_equiv_mid with ⟨mid_gt_2, _2_pow_s_mul_t_equiv_mid⟩
          rcases _2_pow_s_mul_t_equiv_2_pow_s' s' t' mid_gt_2 t'_odd
            with ⟨s'', _2_pow_s''_gt_2, mid_equiv_2_pow_s''⟩
          use s'', _2_pow_s''_gt_2
          --exact Trans.trans _2_pow_s_mul_t_equiv_mid mid_equiv_2_pow_s'' -- "failed to synthesize"
          exact isEquivCondition.trans ⟨2 ^ s * t, left_gt_2⟩ ⟨2 ^ s' * t', mid_gt_2⟩ ⟨2 ^ s'', _2_pow_s''_gt_2⟩ _2_pow_s_mul_t_equiv_mid mid_equiv_2_pow_s''
      termination_by t
      decreasing_by
        have : (t + 1) / 2 < t := by omega
        have : t' ≤ (t + 1) / 2 := by
          rw [half_t_add_one_eq_2_pow_e_mul_t']
          calc
            t' = 1 * t' := by simp
            _ ≤ 2 ^ e * t' := by gcongr; exact Nat.one_le_two_pow -- `omage` doesn't work here
        linarith
      have : 2 ^ s * t > 2 := by rw [←a_eq_2_pow_s_mul_t]; exact a_gt_2
      rcases _2_pow_s_mul_t_equiv_2_pow_s' s t this (by omega) with ⟨s', _2_pow_s'_gt_2, _2_pow_s_mul_t_equiv_2_pow_s'⟩
      use s', _2_pow_s'_gt_2
      subst a_eq_2_pow_s_mul_t
      exact _2_pow_s_mul_t_equiv_2_pow_s'
    }
    --Since $\frac{t+1}{2}$ is an integer, we have $2^{s}, 3 \cdot 2^{s}, 3 \cdot 2^{s-1}, 3 \cdot 2^{s-2}, \ldots, 3$.
    have _2_pow_s_equiv_3 s left_gt_2 : ⟨2 ^ s, left_gt_2⟩ ⇔ 3 := by {
      unfold Condition
      use s + 2
      constructor
      . simp
      . let n
        | 0 => 2 ^ s
        | i' + 1 => if i' ≤ s then 3 * 2 ^ (s - i') else 0
        use n
        constructor
        . intro i _
          unfold n
          split
          . simp
          . split
            . simp
            . linarith -- index contradiction here
        . constructor
          . rfl
          . constructor
            . unfold n
              norm_num
              rfl
            . intro i _
              unfold n
              match i with
              | 0 =>
                norm_num
                have : s > 1 := (Nat.pow_lt_pow_iff_right (show 1 < 2 by simp)).mp left_gt_2
                have : s ≥ 2 := by omega
                rw [show 2 ^ s + 3 * 2 ^ s = 2 ^ (s + 2) by ring]
                use 3 * 2 ^ (s - 2)
                have : 2 ^ (s + 2) * (3 * 2 ^ (s - 2)) = 3 * 2 ^ (2 * s) := by
                  calc
                    2 ^ (s + 2) * (3 * 2 ^ (s - 2)) =  3 * 2 ^ ((s + 2) + (s - 2)) := by ring
                    _ = 3 * 2 ^ (2 * s) := by congr; omega
                rw [this]
                ring
              | i' + 1 =>
                simp [show i' ≤ s by omega, show i' + 1 ≤ s by omega]
                let j := s - (i' + 1)
                rw [show s - (i' + 1) = j by rfl, show s - i' = j + 1 by omega]
                use 2 ^ (j + 1)
                ring
    }
    intro a
    rcases a_equiv_2_pow_s a with ⟨s, _2_pow_s_gt, a_equiv_2_pow_s⟩
    apply trans a_equiv_2_pow_s (_2_pow_s_equiv_3 s _2_pow_s_gt)
  }

  exact Trans.trans (equiv_3 a) (symm (equiv_3 b))
}

end number_theory_604468
open number_theory_604468
