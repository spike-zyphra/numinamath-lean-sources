import Mathlib

namespace algebra_604207

lemma iterate_sub_id_eq_nsmul_sub_id (f g : ℝ → ℝ)
    (h : ∀ x, f x + g x = 2 * x)
    (hfg : ∀ x, f (g x) = x ∧ g (f x) = x) :
    ∀ n : ℕ, f^[n] - id = n • (f - id) := by
  intro n
  have h1 (n : ℕ) : f^[n + 2] - f^[n + 1] = f^[n + 1] - f^[n] := by
    ext x
    -- Plug $x \rightarrow f_{n+1}(x)$ in (2)
    have h11 := h (f^[n + 1] x)
    -- since $g\left(f_{n+1}(x)\right)=g\left(f\left(f_{n}(x)\right)\right)=f_{n}(x)$
    have h12 : g (f^[n + 1] x) = f^[n] x :=
      calc
        _ = g (f (f^[n] x)) := by
          congr 1
          exact Function.iterate_succ_apply' f n x
        _ = f ^[n] x := by rw [(hfg (f^[n] x)).2]
    -- $$ f_{n+2}(x)+f_{n}(x)=2 f_{n+1}(x) $$
    rw [h12] at h11
    rw [show (f (f^[n + 1] x) = f^[n + 2] x) by simp [Function.iterate_succ_apply']] at h11
    simp only [Pi.sub_apply, Function.comp_apply]
    -- that is,$$ f_{n+2}(x)-f_{n+1}(x)=f_{n+1}(x)-f_{n}(x) $$
    linarith only [h11]
  -- Therefore $f_{n}(x)-f_{n-1}(x)$ does not depend on $n$, and is equal to $f(x)-x$.
  have h_diff_const (n : ℕ) : f^[n + 1] - f^[n] = f - id := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show f^[n + 1 + 1] = f^[n + 2] by rfl]
      rw [h1 n, ih]
  -- Induction on $n$, we find $$ f_{n}(x)-x=n(f(x)-x) . $$
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = f^[n + 1] - f^[n] + f^[n] - id := by simp
      _ = (f^[n] - id) + (f - id) := by
        rw [h_diff_const n]
        ring
      _ = (n + 1) • (f - id) := by
        rw [ih]
        ring

end algebra_604207

open algebra_604207

/- Determine all functions $f$ from the reals to the reals for which
(1) $f(x)$ is strictly increasing,
(2) $f(x)+g(x)=2 x$ for all real $x$, where $g(x)$ is the composition inverse function to $f(x)$.
(Note: $f$ and $g$ are said to be composition inverses if $f(g(x))=x$ and $g(f(x))=x$ for all real x.)
Answer: $f(x)=x+c, c \in \mathbb{R}$ constant. -/
theorem algebra_604207 {f g : ℝ → ℝ}
    (hf : StrictMono f) (h : ∀ x, f x + g x = 2 * x)
    (hfg : ∀ x, f (g x) = x ∧ g (f x) = x) :
    ∃ c, ∀ x, f x = x + c := by
  have hf1 := iterate_sub_id_eq_nsmul_sub_id f g h hfg
  -- Since $g$ has the same properties as $f$, $$ g_{n}(x)-x=n(g(x)-x)=-n(f(x)-x) . $$
  have hg1 : ∀ n : ℕ, g^[n] - id = n • (g - id) := by
    apply iterate_sub_id_eq_nsmul_sub_id g f
    · conv at h =>
        enter [x, 1]
        rw [add_comm]
      exact h
    · intro x
      exact ⟨(hfg x).2, (hfg x).1⟩
  -- Finally, $g$ is also increasing,
  -- because since $f$ is increasing $g(x)&gt;g(y) \Longrightarrow f(g(x))&gt;$ $f(g(y)) \Longrightarrow x&gt;y$.
  have hg : StrictMono g := by
    intro x y hxy
    rw [← StrictMono.lt_iff_lt hf]
    rw [(hfg x).1, (hfg y).1]
    exact hxy
  simp only [sub_eq_iff_eq_add] at hf1 hg1
  -- An induction proves that $f_{n}$ and $g_{n}$ are also increasing functions.
  have hfn := StrictMono.iterate hf
  have hgn := StrictMono.iterate hg
  replace hg1 (n : ℕ):  g^[n] = id - (n • (f - id)) := by
    have : g = 2 • id - f := by
      ext x
      simp only [nsmul_eq_mul, Nat.cast_ofNat, Pi.sub_apply, Pi.mul_apply, Pi.ofNat_apply, id_eq]
      rw [← h x]
      rw [add_sub_cancel_left]
    nth_rw 2 [this] at hg1
    rw [hg1]
    ext x
    simp only [nsmul_eq_mul, Nat.cast_ofNat, Pi.natCast_def, Pi.add_apply, Pi.mul_apply,
      Pi.sub_apply, Pi.ofNat_apply, id_eq, Pi.neg_apply, add_left_inj]
    ring
  have h1 (n : ℕ) {x y : ℝ} (hxy : x > y) : n * ((f x - x) - (f y - y)) > y - x := by
    -- Since $f_{n}$ and $g_{n}$ are increasing,
    have : f^[n] x > f^[n] y := by
      apply hfn
      exact hxy
    rw [hf1] at this
    simp only [nsmul_eq_mul, Pi.natCast_def, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, id_eq,
      gt_iff_lt] at this
    -- $$ x+n(f(x)-x)&gt;y+n(f(y)-y) \Longleftrightarrow n[(f(x)-x)-(f(y)-y)]&gt;y-x $$
    linarith only [this]
  have h2 (n : ℕ) {x y : ℝ} (hxy : x > y) : n * ((f x - x) - (f y - y)) < x - y := by
    have : g^[n] x > g^[n] y := by
      apply hgn
      exact hxy
    rw [hg1] at this
    simp only [nsmul_eq_mul, Pi.natCast_def, Pi.add_apply, Pi.neg_apply, Pi.mul_apply, Pi.sub_apply,
      id_eq, gt_iff_lt, lt_neg_add_iff_add_lt] at this
    -- and $$ x-n(f(x)-x)&gt;y-n(f(y)-y) \Longleftrightarrow n[(f(x)-x)-(f(y)-y)] &lt; x - y $$
    linarith only [this]
  -- Suppose that $a=f(x)-x$ and $b=f(y)-y$ are distinct. Then, for all positive integers $n$,
  -- $$ |n(a-b)|&lt;x-y $$
  have h3 (n : ℕ) {x y : ℝ} (hxy : x > y) : |n * ((f x - x) - (f y - y))| < x - y := by
    rw [abs_lt]
    simp only [neg_sub]
    exact ⟨h1 n hxy, h2 n hxy⟩
  have h4 {x y : ℝ} (hxy : x > y) : f x - x = f y - y := by
    rw [← sub_eq_zero]
    by_contra h
    -- which is false for a sufficiently large $n$.
    let n : ℕ := Nat.ceil (2 * (x - y) / |f x - x - (f y - y)|)
    have hnle : 2 * (x - y) / |f x - x - (f y - y)| ≤ n :=
      Nat.le_ceil (2 * (x - y) / |f x - x - (f y - y)|)
    have hn := h3 n hxy
    absurd hn
    simp only [not_lt]
    calc
      _ ≤ 2 * (x - y) := by linarith only [hxy]
      _ = (2 * (x - y) / |f x - x - (f y - y)|) * |f x - x - (f y - y)| := by field_simp only [h]
      _ ≤ n * |f x - x - (f y - y)| := by gcongr
      _ = _ := by
        rw [abs_mul]
        simp only [Nat.abs_cast]
  -- Hence $a=b$, and $f(x)-x$ is a constant $c$ for all $x \in \mathbb{R}$,
  replace h4 (x y : ℝ) : f x - x = f y - y := by
    by_cases h : x = y
    · rw [h]
    · rw [← ne_eq] at h
      rw [ne_iff_lt_or_gt] at h
      rcases h with (hyx | hxy)
      · exact (h4 hyx).symm
      · exact h4 hxy
  -- that is, $f(x)=x+c$. It is immediate that $f(x)=x+c$ satisfies the problem, as $g(x)=x-c$.
  conv =>
    enter [1, c, x]
    rw [add_comm, ← sub_eq_iff_eq_add]
  use f 0 - 0
  intro x
  rw [h4]
