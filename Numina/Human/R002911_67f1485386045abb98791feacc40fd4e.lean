import Mathlib
/-2. A natural number $k$ is given. For $n \in \mathbb{N}$ we define $f_{k}(n)$ as the smallest integer greater than $k n$ such that $n f_{k}(n)$ is a perfect square. Prove that $f_{k}(m)=f_{k}(n)$ implies $m=n$.
(Nikola Petrović)-/
theorem number_theory_129056 (k : ℕ) (hk : k > 0) (f : ℕ → ℕ) (hf : ∀ n, IsLeast {x : ℕ | x > k * n ∧ IsSquare (x * n)} (f n)) (m n : ℕ) (hmn : f n = f m) : n = m:= by
  -- Define q as the common value of f(n) and f(m)
  let q:= f n
  -- Prove that q = f(n)
  have hqn : q = f n:= by rfl
  -- Prove that q = f(m) using the hypothesis
  have hqm : q = f m:= by rw [←hmn]
  -- Get the least property for f(n)
  have hf1:= hf n
  rw [←hqn] at hf1
  -- Get the least property for f(m)
  have hf2:= hf m
  rw [←hqm] at hf2
  -- Extract the components of the least property for n
  rcases hf1 with ⟨hn1, hn2⟩
  -- Extract the components of the least property for m
  rcases hf2 with ⟨hm1, hm2⟩
  -- Simplify the lowerBounds definitions
  simp [lowerBounds] at hn1 hm1 hn2 hm2
  -- Extract the square property and inequality for n
  rcases hn1 with ⟨hn1, hnsq1⟩
  -- Extract the square property and inequality for m
  rcases hm1 with ⟨hm1, hmsq1⟩
  -- Use the square-free decomposition of q
  have h1:= Nat.sq_mul_squarefree q
  rcases h1 with ⟨a, u, hau, ha⟩
  rw [← hau] at hnsq1
  -- Helper lemma: if b²a is a square and b ≠ 0, then a is a square
  have g1 (a b : ℕ) (hb : b ≠ 0) (hsq : IsSquare (b ^ 2 * a)) : IsSquare a:= by
    -- b² is always a square
    have hbb : IsSquare (b ^ 2):= by exact IsSquare_sq b
    -- Express hsq as an existence statement
    rw [isSquare_iff_exists_sq _] at hsq
    rcases hsq with ⟨c, hc⟩
    -- b² divides b²a
    have hbc : b ^ 2 ∣ (b ^ 2 * a):= by exact Nat.dvd_mul_right (b ^ 2) a
    rw [hc] at hbc
    -- Since b² divides c², b divides c
    replace hbc : b ∣ c:= (Nat.pow_dvd_pow_iff (show 2 ≠ 0 by omega)).mp hbc
    replace hbc:= dvd_iff_exists_eq_mul_right.mp hbc
    rcases hbc with ⟨d, hd⟩
    rw [hd] at hc
    -- Rewrite the equation to show b²a = b²d²
    replace hc : b ^ 2 * a = b ^ 2 * d ^ 2:= by
      calc _ = (b * d) ^ 2:= by rw [hc]
           _ = _:= by ring
    -- Cancel b² from both sides
    replace hc:= Nat.eq_of_mul_eq_mul_left (by positivity) hc
    -- Show that a is a square by exhibiting d
    rw [isSquare_iff_exists_sq _]
    use d
  -- q is non-zero
  have hq0 : q ≠ 0:= by omega
  -- Prove that a*n is a square
  have h : IsSquare (a * n):= by
    -- u is non-zero (contradiction if u = 0)
    have hu0 : u ≠ 0:= by
      by_contra hu0
      subst u
      ring_nf at hau
      omega
    -- Rewrite to show u²(a*n) is a square
    replace hnsq1 : IsSquare (u ^ 2 * (a * n)):= by
      rw [show u ^ 2 * a * n = u ^ 2 * (a * n) by ring] at hnsq1
      exact hnsq1
    -- Apply the helper lemma
    exact g1 (a * n) u hu0 hnsq1
  -- Use square-free decomposition of n
  have hn3:= Nat.sq_mul_squarefree n
  rcases hn3 with ⟨b, v, hvu, hb⟩
  rw [← hvu] at h
  -- Rewrite to show v²(a*b) is a square
  replace h : IsSquare ((v ^ 2) * (a * b)):= by
    rw [show a * (v ^ 2 * b) = v ^ 2 * (a * b) by ring] at h
    exact h
  -- Case analysis: n = 0
  by_cases hn0 : n = 0
  .
    clear hvu
    subst n
    -- If n = 0, then k*0 < 1
    have h11 : k * 0 < 1:= by omega
    -- Apply the least property to get q = 1
    replace hn2:= hn2 h11 (show IsSquare 0 by exact g1 0 q hq0 (g1 (q ^ 2 * 0) q hq0 hnsq1))
    replace hn2 : q = 1:= by omega
    rw [hn2] at hm1
    -- Contradiction: m must be 0 as well
    by_contra hm0
    replace hm0 : m ≥ 1:= by omega
    replace hm0 : k * m ≥ 1:= Right.one_le_mul hk hm0
    omega
  .
    -- Case analysis: m = 0
    by_cases hm0 : m = 0
    .
      clear hvu
      subst m
      -- If m = 0, then k*0 < 1
      have h11 : k * 0 < 1:= by omega
      -- Apply the least property to get q = 1
      replace hm2:= hm2 h11 (show IsSquare 0 by exact g1 0 q hq0 (g1 (q ^ 2 * 0) q hq0 hmsq1))
      replace hm2 : q = 1:= by omega
      rw [hm2] at hn1
      -- Contradiction: n must be 0 as well
      by_contra hn0
      replace hn0 : n ≥ 1:= by omega
      replace hn0 : k * n ≥ 1:= Right.one_le_mul hk hn0
      omega
    .
      -- v is non-zero (contradiction if v = 0)
      have hv0 : v ≠ 0:= by
          by_contra hu0
          subst v
          ring_nf at hvu
          omega
      -- Apply helper lemma to show a*b is a square
      replace h:= g1 (a * b) v hv0 h
      -- Helper lemma: if a and b are square-free and a*b is a square, then a = b
      have g2 (a b : ℕ) (_ : a ≠ 0) (hb0 : b ≠ 0) (ha1 : Squarefree a) (hb1 : Squarefree b) (hab : IsSquare (a * b)) : a = b:= by
        -- Express hab as an existence statement
        rw [isSquare_iff_exists_sq _] at hab
        rcases hab with ⟨c, hc⟩
        replace hc : a * b = c ^ 2 * 1:= by omega
        rw [(show c ^ 2 = c * c by ring)] at hc
        -- c² divides a*b
        have hc1 : c * c ∣ a * b:= dvd_iff_exists_eq_mul_right.mpr ⟨1, hc⟩
        -- Since a is square-free and c² divides a*b, c divides a
        have hac:= Squarefree.dvd_of_squarefree_of_mul_dvd_mul_right ha1 hc1
        -- Since b is square-free and c² divides a*b, c divides b
        have hbc:= Squarefree.dvd_of_squarefree_of_mul_dvd_mul_left hb1 hc1
        replace hac:= dvd_iff_exists_eq_mul_right.mp hac
        replace hbc:= dvd_iff_exists_eq_mul_right.mp hbc
        rcases hac with ⟨d, hd⟩
        rcases hbc with ⟨e, he⟩
        rw [hd, he] at hc
        -- Rewrite to show c²(e*d) = c²*1
        replace hc : c * c * (e * d) = c * c * 1:= by
            calc _ = (c * e) * (c * d):= by ring
                _ = _:= by rw [hc]
        -- c is positive
        have hc0 : 0 < c:= by
          by_contra hc0
          replace hc0 : c = 0:= by omega
          subst c
          omega
        replace hc0 : 0 < c * c:= Nat.mul_pos hc0 hc0
        -- Cancel c² from both sides
        replace hc:= Nat.eq_of_mul_eq_mul_left hc0 hc
        -- e = 1 and d = 1
        have he1 : e = 1:= Nat.eq_one_of_mul_eq_one_right hc
        have hd1 : d = 1:= Nat.eq_one_of_mul_eq_one_left hc
        subst e d
        linarith
      -- Apply the helper lemma to get a = b
      have hab:= g2 a b (Squarefree.ne_zero ha) (Squarefree.ne_zero hb) ha hb h
      subst b
      -- Helper lemma: u is the least integer such that u² > v²*k
      have g3 (n q v u a : ℕ) (hfn : f n = q) (hn : v ^ 2 * a = n) (hq : u ^ 2 * a = q) (ha : Squarefree a) : IsLeast {x : ℕ | x ^ 2 > v ^ 2 * k} u:= by
        replace hf:= hf n
        rw [hfn] at hf
        rcases hf with ⟨hq1, hq2⟩
        constructor
        .
          -- Show that u² > v²*k
          simp at hq1 ⊢
          rw [← hn, ←hq] at hq1
          rcases hq1 with ⟨hq1, hq3⟩
          replace hq1 : v ^ 2 * k * a < u ^ 2 * a:= by
            rw [show k * (v ^ 2 * a) = v ^ 2 * k * a by ring] at hq1
            exact hq1
          exact Nat.lt_of_mul_lt_mul_right hq1
        .
          -- Show that u is the least such integer
          simp [lowerBounds] at hq1 hq2 ⊢
          intro u1 hu1
          let q1:= u1 ^ 2 * a
          have hq11 : q1 = u1 ^ 2 * a:= by rfl
          have ha0 : a ≠ 0:= Squarefree.ne_zero ha
          -- Show that k*n < q1
          have hq12 : k * n < q1:= by
            rw [← hn, hq11]
            rw [show k * (v ^ 2 * a) = v ^ 2 * k * a by ring]
            refine Nat.mul_lt_mul_of_pos_right hu1 (by  omega)
          replace hq2:= hq2 hq12
          -- Show that q1*n is a square
          have hq1sq : IsSquare (q1 * n):= by
            rw [hq11, ← hn]
            rw [show u1 ^ 2 * a * (v ^ 2 * a) = (u1 * a * v) ^ 2 by ring]
            exact IsSquare_sq (u1 * a * v)
          replace hq2:= hq2 hq1sq
          rw [← hq, hq11] at hq2
          -- u² ≤ u1²
          replace hq2 : u ^ 2 ≤ u1 ^ 2:= Nat.le_of_mul_le_mul_right hq2 (by positivity)
          replace hq2 : (u : ℤ) ^ 2 ≤ (u1 : ℤ) ^ 2:= by exact_mod_cast hq2
          have hu0 : 0 ≤ (u1 : ℤ):= by positivity
          -- |u| ≤ |u1|
          replace hq2:= abs_le_of_sq_le_sq' hq2 hu0
          linarith
      -- Apply the helper lemma for n
      have gun:= g3 n q v u a (by rfl) hvu hau ha
      rw [← hau] at hmsq1
      -- u is non-zero (contradiction if u = 0)
      have hu0 : u ≠ 0:= by
        by_contra hu0
        subst u
        ring_nf at hau
        omega
      -- Prove that a*m is a square
      have hm : IsSquare (a * m):= by
        replace hmsq1 : IsSquare (u ^ 2 * (a * m)):= by
          rw [show u ^ 2 * a * m = u ^ 2 * (a * m) by ring] at hmsq1
          exact hmsq1
        exact g1 (a * m) u hu0 hmsq1
      -- Use square-free decomposition of m
      have hm3:= Nat.sq_mul_squarefree m
      rcases hm3 with ⟨b, w, hwu, hb⟩
      rw [← hwu] at hm
      -- Rewrite to show w²(a*b) is a square
      replace hm : IsSquare ((w ^ 2) * (a * b)):= by
        rw [show a * (w ^ 2 * b) = w ^ 2 * (a * b) by ring] at hm
        exact hm
      -- w is non-zero (contradiction if w = 0)
      have hw0 : w ≠ 0:= by
        by_contra hu0
        subst w
        ring_nf at hwu
        omega
      -- Apply helper lemma to show a*b is a square
      replace hm:= g1 (a * b) w hw0 hm
      -- Apply the helper lemma to get a = b
      have hab:= g2 a b (Squarefree.ne_zero ha) (Squarefree.ne_zero hb) ha hb hm
      subst b
      -- Apply the helper lemma for m
      have gum:= g3 m q w u a (by linarith) hwu hau ha

      -- Extract the components of the least property for n
      rcases gun with ⟨huv, huv1⟩
      -- Extract the components of the least property for m
      rcases gum with ⟨huw, huw1⟩
      simp [lowerBounds] at huv huv1 huw huw1
      -- Case analysis: u ≤ 1
      by_cases hu0 : u ≤ 1
      .
        -- If u ≤ 1, then u = 1
        replace hu0 : u = 1:= by omega
        subst u
        replace hk : k ≥ 1:= by omega
        -- v² ≤ v²*k
        have hvk : v ^ 2 ≤ v ^ 2 * k:= Nat.le_mul_of_pos_right (v ^ 2) hk
        -- v² < 1, so v < 1
        replace huv : v ^ 2 < 1:= by linarith
        replace huv : v < 1:= lt_of_pow_lt_pow_left' 2 huv
        omega
      .
        -- u > 1
        replace hu0 : u > 1:= by omega
        -- Case analysis: v > w
        by_cases hvw : v > w
        .
          -- Show that w²*k < (u-1)²
          have huw2 : w ^ 2 * k < (u - 1) ^ 2:= by
            have hv0 : v ≥ 0:= by omega
            have hw0 : w ≥ 0:= by omega
            replace hk : 1 ≤ k:= by omega
            replace hvw : v ≥ w + 1:= by omega
            have huu0:= hu0
            rify at hu0 hv0 hw0 huv hvw hk ⊢
            -- √(v²*k) < √(u²)
            replace huv : √(v ^ 2 * k) < √(u ^ 2):= by
              refine (Real.sqrt_lt_sqrt_iff_of_pos (by positivity)).mpr huv
            have hu11 : ↑(u - 1) = ↑u - (1 : ℝ):= Nat.cast_pred (by omega)
            have hu00 : (0 : ℝ) < ↑(u - 1) ^ 2:= by
              rw [hu11]
              replace hu0 : 0 < (u : ℝ) - 1:= by linarith
              exact sq_pos_of_pos hu0
            rw [←Real.sqrt_lt_sqrt_iff_of_pos hu00]
            field_simp at huv ⊢
            -- (w+1)*√k ≤ v*√k
            replace hvw : (↑w + 1) * √↑k ≤ ↑v * √↑k:= mul_le_mul_of_nonneg_right hvw (by positivity)
            replace hvw : (↑w + 1) * √↑k < ↑u:= by linarith
            have hk1 : 1 ≤ √↑k:= Real.one_le_sqrt.mpr hk
            rw [show (↑w + 1) * √↑k = ↑w * √↑k + √↑k by ring] at hvw
            replace hvw : ↑w * √↑k + 1 < ↑u:= by linarith
            rw [show √((↑u - 1) ^ 2) = ↑u - 1 by refine Real.sqrt_sq (by linarith)]
            linarith
          -- Apply the least property to get contradiction
          replace huw1:= huw1 huw2
          omega
        .
          -- Case analysis: v = w
          by_cases hvw1 : v = w
          .
            -- If v = w, then n = m
            subst w
            linarith
          .
            -- v < w
            replace hvw1 : w - v ≠ 0:= by omega
            replace hvw : v < w:= by refine Nat.sub_ne_zero_iff_lt.mp hvw1
            -- Show that v²*k < (u-1)²
            have huw2 : v ^ 2 * k < (u - 1) ^ 2:= by
              have hv0 : v ≥ 0:= by omega
              have hw0 : w ≥ 0:= by omega
              replace hk : 1 ≤ k:= by omega
              replace hvw : w ≥ v + 1:= by omega
              rify at hu0 hv0 hw0 huv huw hvw hwu hk ⊢
              -- √(w²*k) < √(u²)
              replace huw : √(w ^ 2 * k) < √(u ^ 2):= by
                refine (Real.sqrt_lt_sqrt_iff_of_pos (by positivity)).mpr huw
              have hu11 : ↑(u - 1) = ↑u - (1 : ℝ):= Nat.cast_pred (by omega)
              have hu00 : (0 : ℝ) < ↑(u - 1) ^ 2:= by
                rw [hu11]
                replace hu0 : 0 < (u : ℝ) - 1:= by linarith
                exact sq_pos_of_pos hu0
              rw [←Real.sqrt_lt_sqrt_iff_of_pos hu00]
              field_simp at huw ⊢
              -- (v+1)*√k ≤ w*√k
              replace hvw : (↑v + 1) * √↑k ≤ ↑w * √↑k:= mul_le_mul_of_nonneg_right hvw (by positivity)
              replace hvw : (↑v + 1) * √↑k < ↑u:= by linarith
              have hk1 : 1 ≤ √↑k:= Real.one_le_sqrt.mpr hk
              rw [show (↑v + 1) * √↑k = ↑v * √↑k + √↑k by ring] at hvw
              replace hvw : ↑v * √↑k + 1 < ↑u:= by linarith
              rw [show √((↑u - 1) ^ 2) = ↑u - 1 by refine Real.sqrt_sq (by linarith)]
              linarith
            -- Apply the least property to get contradiction
            replace huv1:= huv1 huw2
            omega
