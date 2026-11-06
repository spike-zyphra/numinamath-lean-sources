import Mathlib

set_option linter.dupNamespace false

namespace number_theory_170366

def x (n : ℕ) : ℤ := match n with
  | 0 => 1
  | 1 => 1
  | n + 2 => x (n + 1) + 2 * x n

def y (n : ℕ) : ℤ := match n with
  | 0 => 1
  | 1 => 7
  | n + 2 => 2 * y (n + 1) + 3 * y n

/- $Example 6 Define the integer sequences $\left\{x_{n}\right\}$ and $\left\{y_{n}\right\}$:
$$
\begin{array}{l}
x_{0}=1, x_{1}=1, x_{n+1}=x_{n}+2 x_{n-1}(n \geqslant 1) ; \\
y_{0}=1, y_{1}=7, y_{n+1}=2 y_{n}+3 y_{n-1}(n \geqslant 1) .
\end{array}
$$

Prove: These two sequences have no common terms other than 1. -/
theorem number_theory_170366 :
    ∀ m n, x m = y n → x m = 1 /- ∧ y n = 1 -/ := by
  -- 【分析】由于 $\left\{x_{n}\right\} 、\left\{y_{n}\right\}$ 均为二阶递归数列, 故它们的模数列为周期数列.
  -- 若能找到一个模 $m$, 使得当 $n \geqslant 1$ 时, $\left\{x_{n}(\bmod m)\right\} 、\left\{y_{n}(\bmod m)\right\}$ 中的项各不相同,这就证明了本题. 经过多次尝试发现 $\left\{x_{n}(\bmod 8)\right\}: 1,1,3,5,3,5,3,5, \cdots$, 是从第三项开始的周期为 2 的周期数列; $\left\{y_{n}(\bmod 8)\right\}: 1,7,1,7,1,7, \cdots$, 是周期为 2 的纯周期数列.
  let rec x_mod_8_eq : ∀ n ≥ 2, x n % 8 = match n % 2 with | 0 => 3 | _ => 5
    | 2, _ => rfl
    | 3, _ => rfl
    | n' + 4, _ => by
      unfold x
      --norm_num
      have : (x (n' + 2 + 1) + 2 * x (n' + 2)) % 8 = (x (n' + 2 + 1) % 8 + 2 * (x (n' + 2) % 8)) % 8 := by
        omega
      rw [this]
      have := x_mod_8_eq (n' + 2) (by linarith)
      rw [this]
      rw [x_mod_8_eq (n' + 3) (by linarith)]
      repeat rw [Nat.add_mod n']
      mod_cases n'_mod_eq : n' % 2 <;>
      . rw [n'_mod_eq]
        rfl
  let rec y_mod_8_eq : ∀ n, y n % 8 = match n % 2 with | 0 => 1 | _ => 7
    | 0 => rfl
    | 1 => rfl
    | n' + 2 => by
      unfold y
      have : (2 * y (n' + 1) + 3 * y (n')) % 8 = (2 * (y (n' + 1) % 8) + 3 * (y n' % 8)) % 8 := by
        omega
      rw [this]
      rw [y_mod_8_eq (n' + 1)]
      rw [y_mod_8_eq n']
      repeat rw [Nat.add_mod n']
      mod_cases n'_mod_eq : n' % 2 <;>
      . rw [n'_mod_eq]
        rfl
  -- 因此发现当 $n \geqslant 3$ 时, $\left\{x_{n}(\bmod 8)\right\}$ 、 $\left\{y_{n}(\bmod 8)\right\}$ 没有相同的项. 结论得证.
  intro m n x_m_eq_y_n
  match m with
  | 0 => rfl
  | 1 => rfl
  | m' + 2 =>
    let m := m' + 2
    have : m ≥ 2 := by linarith
    have x_m_eqs : x m % 8 = 3 ∨ x m % 8 = 5 := by
      have := x_mod_8_eq m this
      rw [this]
      match m % 2 with
      | 0 => simp
      | _ + 1 => simp -- The `_ + 1` pattern has to be written explicitly for the goal to be reduced.
    have y_n_eqs : y n % 8 = 1 ∨ y n % 8 = 7 := by
      have := y_mod_8_eq n
      rw [this]
      match n % 2 with
      | 0 => simp
      | _ + 1 => simp
    exfalso
    have : x m % 8 = y n % 8 := by
      congr
    cases x_m_eqs <;>
    . cases y_n_eqs <;>
      . linarith
  -- 【评注】本题若对数列 $\left\{x_{n}\right\} 、\left\{y_{n}\right\}$ 直接求通项后再对比会比较麻烦, 但选择模 8 后, 可发现数列呈周期性变化, 原问题得到了简化.从题目条件来看, 取模方向并不明确, 需要反复尝试.

end number_theory_170366
open number_theory_170366
