import Mathlib

open Real Set
open scoped BigOperators

/- Soit $n>0$ un entier et $x_{1}, \cdots, x_{n}$ des réels strictement positifs. Prouver que :

$$
\begin{gathered}
\max _{x_{1}>0, \cdots, x_{n}>0} \min \left(x_{1}, \frac{1}{x_{1}}+x_{2}, \cdots, \frac{1}{x_{n-1}}+x_{n}, \frac{1}{x_{n}}\right)= \\
\min _{x_{1}>0, \cdots, x_{n}>0} \max \left(x_{1}, \frac{1}{x_{1}}+x_{2}, \cdots, \frac{1}{x_{n-1}}+x_{n}, \frac{1}{x_{n}}\right)=2 \cos \left(\frac{\pi}{n+2}\right) .
\end{gathered}
$$ -/
theorem inequalities_607516 {n : ℕ} (hn : n > 0) {f : (ℕ → ℝ) → Finset ℝ}
    (hf : ∀ x, f x = {x 1} ∪ ((Finset.Ico 1 n).image (fun i => 1 / (x i) + x (i + 1))) ∪ {1 / x n}) :
    IsGreatest {r | ∃ x : ℕ → ℝ, (∀ i ∈ Finset.Icc 1 n, x i > 0) ∧ IsLeast (f x) r} (2 * cos (π / (n + 2))) ∧
    IsLeast {r | ∃ x : ℕ → ℝ, (∀ i ∈ Finset.Icc 1 n, x i > 0)  ∧ IsGreatest (f x) r} (2 * cos (π / (n + 2))) := by
  -- Soit Ul'ensemble des n -uplets de réels strictement positifs. Pour $x=\left(x_{1}, \cdots, x_{n}\right) \in U$, on pose
  let U := {x : ℕ → ℝ | ∀ i ∈ Finset.Icc 1 n, x i > 0}
  -- $$ \begin{aligned} & \quad m(x)=\min \left(x_{1}, \frac{1}{x_{1}}+x_{2}, \cdots, \frac{1}{x_{n-1}}+x_{n}, \frac{1}{x_{n}}\right) \ & \text { et } M(x)=\max \left(x_{1}, \frac{1}{x_{1}}+x_{2}, \cdots, \frac{1}{x_{n-1}}+x_{n}, \frac{1}{x_{n}}\right) \end{aligned} $$
  have hfne {x : ℕ → ℝ} : (f x).Nonempty := by
    use x 1
    simp [hf]
  let m (x : ℕ → ℝ) := (f x).min' hfne
  let M (x : ℕ → ℝ) := (f x).max' hfne

  -- Notre stratégie va consister à prouver qu'il existe $a \in U$ tel que $m(a)=M(a)$ et que,
  -- pour tout $x \in U$, on a $m(x) \leqslant m(a)$ et $M(a) \leqslant M(x)$.
  suffices h : ∃ a ∈ U, m a = M a ∧ m a = 2 * cos (π / (n + 2)) ∧ ∀ x ∈ U, m x ≤ m a ∧ M a ≤ M x
  · obtain ⟨a, ha, h₁, h₂, h₃⟩ := h
    simp [U] at ha h₃
    simp [←h₂]
    constructor
    · simp [IsGreatest]
      constructor
      · use a, ha
        exact Finset.isLeast_min' (f a) hfne
      · intro r hr
        simp at hr
        obtain ⟨x, hx, hr⟩ := hr
        trans m x
        · simp [IsLeast] at hr
          obtain hr := hr.2
          exact (Finset.le_min'_iff (f x) hfne).mpr hr
        · exact (h₃ x hx).1
    · rw [h₁]
      simp [IsLeast]
      constructor
      · use a, ha
        exact Finset.isGreatest_max' (f a) hfne
      · intro r hr
        simp at hr
        obtain ⟨x, hx, hr⟩ := hr
        trans M x
        · exact (h₃ x hx).2
        · simp [IsGreatest] at hr
          obtain hr := hr.2
          exact (Finset.max'_le_iff (f x) hfne).mpr hr
  · suffices h : ∃ a ∈ U, m a = M a ∧ m a = 2 * cos (π / (↑n + 2))
    · -- Soit $a=\left(a_{1}, \cdots, a_{n}\right) \in U$. La condition $m(a)=M(a)$ s'écrit
      -- $$ a_{1}=\frac{1}{a_{1}}+a_{2}=\cdots=\frac{1}{a_{n-1}}+a_{n}=\frac{1}{a_{n}} . $$
      obtain ⟨a, ha, h₁, h₂⟩ := h
      use a, ha, h₁, h₂
      have hmaeqa1 : m a = a 1 := by
        apply le_antisymm
        · apply Finset.min'_le
          simp [hf]
        · simp [h₁]
          apply Finset.le_max'
          simp [hf]
      have haeqi : ∀ {i : ℕ}, i ∈ Finset.Ico 1 n → (1 / a i) + a (i + 1) = m a := by
        intro i hi
        simp at hi
        apply le_antisymm
        · rw [h₁]
          apply Finset.le_max'
          simp [hf]
          right; left
          use i
        · apply Finset.min'_le
          simp [hf]
          right; left
          use i
      have haeqn : 1 / a n = m a := by
        apply le_antisymm
        · rw [h₁]
          apply Finset.le_max'
          simp [hf]
        · apply Finset.min'_le
          simp [hf]
      -- Mais, admettons pour le moment que l'on ait déjà trouvé $a \in U$ tel que $m(a)=M(a)$.
      intro x hx
      constructor
      · -- Par l'absurde : On suppose qu'il existe $x \in U$ tel que $m(x)&gt;m(a)$.
        by_contra hlt
        simp at hlt
        -- On prouve alors par récurrence sur $k$ que $x_{k}&gt;\mathfrak{a}_{k}$ pour tout $k \in\{1, \cdots, \mathfrak{n}\}$ :
        have hlt' {k : ℕ} (hk : k ∈ Finset.Icc 1 n) : x k > a k := by
          simp at hk
          obtain h := hk.2
          revert h
          induction k, hk.1 using Nat.le_induction
          · -- Déjà, on a $x_{1} \geqslant m(x)&gt;m(a)=a_{1}$.
            intro
            apply Finset.lt_min'_iff _ hfne |>.mp at hlt
            rw [←hmaeqa1]
            apply hlt
            simp [hf]
          · -- D'autre part, si $x_{k}&gt;a_{k}$ pour un certain $k \in\{1, \cdots, n-1\}$, alors
            -- $$ \frac{1}{x_{k}}+x_{k+1} \geqslant m(x)&gt;m(a)=\frac{1}{a_{k}}+a_{k+1} $$
            rename_i k' hle ih
            intro hk'
            have hin : k' ∈ Finset.Ico 1 n := by simp [hle]; exact hk'
            rw [←haeqi hin] at hlt
            have : 1 / a k' + a (k' + 1) < 1 / x k' + x (k' + 1) := by
              apply Finset.lt_min'_iff _ hfne |>.mp hlt
              simp [hf]
              right; left
              simp at hin
              use k'
            -- Or, d'après l'hypothèse de récurrence, on a $\frac{1}{x_{k}}a_{k+1}$, ce qui achève la récurrence.
            trans  1 / x k' + x (k' + 1) - 1 / a k'
            · apply sub_lt_iff_lt_add.mpr
              rw [add_comm]
              apply add_lt_add_iff_left _ |>.mpr
              apply div_lt_div_of_pos_left (by simp)
              · simp [U] at ha
                simp at hin
                apply ha k'
                · exact hin.1
                · exact le_of_lt hin.2
              · apply ih
                exact Nat.le_of_succ_le hk'
            · linarith only [this]
        -- En particulier, on a donc $x_{n}&gt;a_{n}$.
        have hxn : x n > a n := by
          apply hlt'
          simp
          exact hn
        -- Mais, $\frac{1}{x_{n}} \geqslant m(x)&gt;m(a)=\frac{1}{a_{n}}$, d'où $x_{n}0$ la valeur commune dans (1).
        have : ¬ x n > a n := by
          simp
          apply le_of_lt
          apply lt_of_one_div_lt_one_div
          · simp [U] at ha
            apply ha n
            · exact hn
            · rfl
          · rw [haeqn]
            apply lt_of_lt_of_le hlt
            apply Finset.min'_le
            simp [hf]
        contradiction
      · -- Par le même raisonnement, on prouve que $M(a) \leqslant M(x)$.
        by_contra hlt
        simp at hlt
        -- On prouve alors par récurrence sur $k$ que $a_{k} \leqslant x_{k}$ pour tout $k \in\{1, \cdots, n\}$ :
        have hlt' {k : ℕ} (hk : k ∈ Finset.Icc 1 n) : x k < a k := by
          simp at hk
          obtain h := hk.2
          revert h
          induction k, hk.1 using Nat.le_induction
          · -- Déjà, on a $x_{1} \geqslant m(x)&gt;m(a)=a_{1}$.
            intro
            apply Finset.max'_lt_iff _ hfne |>.mp at hlt
            rw [←hmaeqa1, h₁]
            apply hlt
            simp [hf]
          · -- D'autre part, si $x_{k}&gt;a_{k}$ pour un certain $k \in\{1, \cdots, n-1\}$, alors
            -- $$ \frac{1}{x_{k}}+x_{k+1} \geqslant m(x)&gt;m(a)=\frac{1}{a_{k}}+a_{k+1} $$
            rename_i k' hle ih
            intro hk'
            have hin : k' ∈ Finset.Ico 1 n := by simp [hle]; exact hk'
            rw [←h₁, ←haeqi hin] at hlt
            have : 1 / a k' + a (k' + 1) > 1 / x k' + x (k' + 1) := by
              apply Finset.max'_lt_iff _ hfne |>.mp hlt
              simp [hf]
              right; left
              simp at hin
              use k'
            -- Or, d'après l'hypothèse de récurrence, on a $\frac{1}{x_{k}}a_{k+1}$, ce qui achève la récurrence.
            trans  1 / a k' + a (k' + 1) - 1 / x k'
            · linarith [this]
            · apply sub_lt_iff_lt_add.mpr
              rw [add_comm]
              apply add_lt_add_iff_left _ |>.mpr
              apply div_lt_div_of_pos_left (by simp)
              · simp [U] at hx
                simp at hin
                apply hx k'
                · exact hin.1
                · exact le_of_lt hin.2
              · apply ih
                exact Nat.le_of_succ_le hk'
        -- En particulier, on a donc $x_{n}&gt;a_{n}$.
        have hxn : x n < a n := by
          apply hlt'
          simp
          exact hn
        -- Mais, $\frac{1}{x_{n}} \geqslant m(x)&gt;m(a)=\frac{1}{a_{n}}$, d'où $x_{n}0$ la valeur commune dans (1).
        have : ¬ x n < a n := by
          simp
          apply le_of_lt
          apply lt_of_one_div_lt_one_div
          · simp [U] at hx
            apply hx n
            · exact hn
            · rfl
          · rw [haeqn, h₁]
            apply lt_of_le_of_lt ?_ hlt
            apply Finset.le_max'
            simp [hf]
        contradiction
    · -- où $a_{k}=\frac{\sin \left(\frac{(k+1) \pi}{n+2}\right)}{\sin \left(\frac{k \pi}{n+2}\right)}$.
      let a : ℕ → ℝ := fun k => sin ((k + 1) * π / (n + 2)) / sin (k * π / (n + 2))
      have hpos {k : ℕ} (hk : k ∈ Finset.Icc 1 (n + 1)) : sin (k * π / (n + 2)) > 0 := by
        apply Real.sin_pos_of_mem_Ioo
        simp at hk ⊢
        constructor
        · apply div_pos ?_ (by norm_cast; simp)
          apply mul_pos (by norm_cast; exact hk.1) pi_pos
        · apply div_lt_iff₀ (by norm_cast; simp) |>.mpr
          rw [mul_comm]
          apply mul_lt_mul_of_pos_left ?_ pi_pos
          norm_cast
          apply lt_of_lt_of_eq
          · exact Nat.lt_add_one_of_le hk.2
          · simp
      have ha : a ∈ U := by
        simp [U]
        intro i hi₁ hi₂
        simp [a]
        apply div_pos
        · have : i + 1 ∈ Finset.Icc 1 (n + 1) := by simp; exact hi₂
          obtain h := hpos this
          simp at h
          exact h
        · apply hpos
          simp [hi₁]
          exact Nat.le_add_right_of_le hi₂
      use a, ha
      --  Compte-tenu de la formule bien connue
      -- $$ 2 \cos (a) \sin (b)=\sin (b+a)+\sin (b-a) $$
      -- une autre récurrence sans difficulté à partir de (2) conduit alors à
      have h : ∀ r ∈ f a, r = 2 * cos (π / (n + 2)) := by
        simp [hf, a]
        have heq : sin (2 * (π / (↑n + 2))) / sin (π / (↑n + 2)) = 2 * cos (π / (↑n + 2)) := by
          calc
            _ = 2 * sin (π / (↑n + 2)) * cos (π / (↑n + 2)) / sin (π / (↑n + 2)) := by simp [sin_two_mul]
            _ = 2 * (sin (π / (↑n + 2)) * cos (π / (↑n + 2)) / sin (π / (↑n + 2))) :=  by ring
            _ = _ := by
              rw [mul_div_cancel_left₀]
              apply ne_of_gt
              obtain h := @hpos 1 (by simp)
              simp at h
              exact h
        split_ands
        · norm_num
          rw [←heq]
          congr; ring
        · intro a ha
          rcases ha with ha | ha
          · obtain ⟨i, hi, ha⟩ := ha
            rw [←ha]
            obtain hden := @hpos (i + 1) (by simp; apply le_of_lt hi.2)
            simp at hden
            field_simp
            rw [show sin (↑i * π / (↑n + 2)) + sin ((↑i + 1 + 1) * π / (↑n + 2)) = sin ((↑i + 1) * π / (↑n + 2) - (π / (↑n + 2))) + sin ((↑i + 1) * π / (↑n + 2) +  π / (↑n + 2)) by ring_nf]
            rw [sin_add, sin_sub]
            ring
          · rw [ha]
            rw [show n * π / (↑n + 2) = π - 2 * (π / (↑n + 2)) by field_simp; ring]
            rw [show (n + 1) * π / (↑n + 2) = π - (π / (↑n + 2)) by field_simp; ring]
            rw [sin_pi_sub, sin_pi_sub]
            exact heq
      -- calculons $m(a)$ et $M(a)$ :
      have hM : M a = 2 * cos (π / (n + 2)) := by
        have : ∃ r ∈ f a, M a = r := by exact Finset.exists_mem_eq_sup' hfne id
        obtain ⟨r, hr, hr'⟩ := this
        rw [hr']
        apply h r hr
      have hm : m a = 2 * cos (π / (n + 2)) := by
        have : ∃ r ∈ f a, m a = r := by exact Finset.exists_mem_eq_inf' hfne id
        obtain ⟨r, hr, hr'⟩ := this
        rw [hr']
        apply h r hr
      -- On a donc $m(a)=M(a)$.
      simp [hM, hm]
