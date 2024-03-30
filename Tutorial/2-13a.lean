import «Tutorial».Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic


open GateauxDeriv Matrix Topology
-- 2.13(a)

-- 计算 a^T Xb 的导数，大致思路为容易验证导数 D 应当满足 D . V = a^T V b，取 D = a^T b ，分别验证两个等式即可
-- 主要困难在于需要用开集的条件规约出tendsTo 内部的 t != 0，
-- 这里通过用 eventuallyEq_nhdsWithin_of_eqOn 证明引理引导 apply tendsto_congr' 自动匹配解决
theorem problem_a (a : Fin m → ℝ) (X : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ)
  : HasGateauxDerivAt (f_aXb a b) X (vecMulVec a b) := by
    simp [HasGateauxDerivAt]
    simp [Matrix.add_mulVec]
    simp [Matrix.smul_mulVec_assoc]
    simp [← div_mul_eq_mul_div]
    intro V
    have : innerProductofMatrix (vecMulVec a b) V = a ⬝ᵥ mulVec V b := by
      rw [<- f_aXb]
      apply Eq.symm
      apply f_aXb_eq
    rw [this]
    have : (fun t => t / t * a ⬝ᵥ mulVec V b) =ᶠ[𝓝[≠] 0] (fun _ => a ⬝ᵥ mulVec V b) := by
      apply eventuallyEq_nhdsWithin_of_eqOn
      intro x h
      simp
      rw [div_self (h), one_mul]
    apply (Filter.tendsto_congr' this).mpr
    apply tendsto_const_nhds


/--proof and state-/

theorem problem_a_state (a : Fin m → ℝ) (X : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ)
  : HasGateauxDerivAt (f_aXb a b) X (vecMulVec a b) := by
    /-
    m n: ℕ
    a: Fin m → ℝ
    X: Matrix (Fin m) (Fin n) ℝ
    b: Fin n → ℝ
    ⊢ HasGateauxDerivAt (f_aXb a b) X (vecMulVec a b)
    -/
    simp [HasGateauxDerivAt]
    /-m n: ℕ
    a: Fin m → ℝ
    X: Matrix (Fin m) (Fin n) ℝ
    b: Fin n → ℝ
    ⊢ ∀ (V : Matrix (Fin m) (Fin n) ℝ), Filter.Tendsto (fun t => (a ⬝ᵥ mulVec (X + t • V) b - a ⬝ᵥ mulVec X b) / t) (𝓝[≠] 0) (𝓝 (innerProductofMatrix (vecMulVec a b) V))
    -/
    simp [Matrix.add_mulVec]
    /-m n: ℕ
    a: Fin m → ℝ
    X: Matrix (Fin m) (Fin n) ℝ
    b: Fin n → ℝ
    ⊢ ∀ (V : Matrix (Fin m) (Fin n) ℝ), Filter.Tendsto (fun t => a ⬝ᵥ mulVec (t • V) b / t) (𝓝[≠] 0) (𝓝 (innerProductofMatrix (vecMulVec a b) V))-/
    simp [Matrix.smul_mulVec_assoc]
    /-m n: ℕ
    a: Fin m → ℝ
    X: Matrix (Fin m) (Fin n) ℝ
    b: Fin n → ℝ
    ⊢ ∀ (V : Matrix (Fin m) (Fin n) ℝ), Filter.Tendsto (fun t => t * a ⬝ᵥ mulVec V b / t) (𝓝[≠] 0) (𝓝 (innerProductofMatrix (vecMulVec a b) V))-/
    simp [← div_mul_eq_mul_div]
    /-m n: ℕ
    a: Fin m → ℝ
    X: Matrix (Fin m) (Fin n) ℝ
    b: Fin n → ℝ
    ⊢ ∀ (V : Matrix (Fin m) (Fin n) ℝ), Filter.Tendsto (fun t => t / t * a ⬝ᵥ mulVec V b) (𝓝[≠] 0) (𝓝 (innerProductofMatrix (vecMulVec a b) V))-/
    intro V
    /-m n: ℕ
    a: Fin m → ℝ
    X: Matrix (Fin m) (Fin n) ℝ
    b: Fin n → ℝ
    V: Matrix (Fin m) (Fin n) ℝ
    ⊢ Filter.Tendsto (fun t => t / t * a ⬝ᵥ mulVec V b) (𝓝[≠] 0) (𝓝 (innerProductofMatrix (vecMulVec a b) V))-/
    have : innerProductofMatrix (vecMulVec a b) V = a ⬝ᵥ mulVec V b := by
      rw [<- f_aXb]
      apply Eq.symm
      apply f_aXb_eq
    /-m n: ℕ
    a: Fin m → ℝ
    X: Matrix (Fin m) (Fin n) ℝ
    b: Fin n → ℝ
    V: Matrix (Fin m) (Fin n) ℝ
    this: innerProductofMatrix (vecMulVec a b) V = a ⬝ᵥ mulVec V b
    ⊢ Filter.Tendsto (fun t => t / t * a ⬝ᵥ mulVec V b) (𝓝[≠] 0) (𝓝 (innerProductofMatrix (vecMulVec a b) V))-/
    rw [this]
    /-m n: ℕ
    a: Fin m → ℝ
    X: Matrix (Fin m) (Fin n) ℝ
    b: Fin n → ℝ
    V: Matrix (Fin m) (Fin n) ℝ
    this: innerProductofMatrix (vecMulVec a b) V = a ⬝ᵥ mulVec V b
    ⊢ Filter.Tendsto (fun t => t / t * a ⬝ᵥ mulVec V b) (𝓝[≠] 0) (𝓝 (a ⬝ᵥ mulVec V b))-/
    have : (fun t => t / t * a ⬝ᵥ mulVec V b) =ᶠ[𝓝[≠] 0] (fun _ => a ⬝ᵥ mulVec V b) := by
      apply eventuallyEq_nhdsWithin_of_eqOn
      intro x h
      simp
      rw [div_self (h), one_mul]
    /-m n: ℕ
    a: Fin m → ℝ
    X: Matrix (Fin m) (Fin n) ℝ
    b: Fin n → ℝ
    V: Matrix (Fin m) (Fin n) ℝ
    this✝: innerProductofMatrix (vecMulVec a b) V = a ⬝ᵥ mulVec V b
    this: (fun t => t / t * a ⬝ᵥ mulVec V b) =ᶠ[𝓝[≠] 0] fun x => a ⬝ᵥ mulVec V b
    ⊢ Filter.Tendsto (fun t => t / t * a ⬝ᵥ mulVec V b) (𝓝[≠] 0) (𝓝 (a ⬝ᵥ mulVec V b))-/
    apply (Filter.tendsto_congr' this).mpr
    /-m n: ℕ
    a: Fin m → ℝ
    X: Matrix (Fin m) (Fin n) ℝ
    b: Fin n → ℝ
    V: Matrix (Fin m) (Fin n) ℝ
    this✝: innerProductofMatrix (vecMulVec a b) V = a ⬝ᵥ mulVec V b
    this: (fun t => t / t * a ⬝ᵥ mulVec V b) =ᶠ[𝓝[≠] 0] fun x => a ⬝ᵥ mulVec V b
    ⊢ Filter.Tendsto (fun x => a ⬝ᵥ mulVec V b) (𝓝[≠] 0) (𝓝 (a ⬝ᵥ mulVec V b))-/
    apply tendsto_const_nhds
    /-No goals-/


/-no tactic-/
theorem problem_a_notactic (a : Fin m → ℝ) (X : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ)
  : HasGateauxDerivAt (f_aXb a b) X (vecMulVec a b) := by
    /-
    m n: ℕ
    a: Fin m → ℝ
    X: Matrix (Fin m) (Fin n) ℝ
    b: Fin n → ℝ
    ⊢ HasGateauxDerivAt (f_aXb a b) X (vecMulVec a b)
    -/

    /-m n: ℕ
    a: Fin m → ℝ
    X: Matrix (Fin m) (Fin n) ℝ
    b: Fin n → ℝ
    ⊢ ∀ (V : Matrix (Fin m) (Fin n) ℝ), Filter.Tendsto (fun t => (a ⬝ᵥ mulVec (X + t • V) b - a ⬝ᵥ mulVec X b) / t) (𝓝[≠] 0) (𝓝 (innerProductofMatrix (vecMulVec a b) V))
    -/

    /-m n: ℕ
    a: Fin m → ℝ
    X: Matrix (Fin m) (Fin n) ℝ
    b: Fin n → ℝ
    ⊢ ∀ (V : Matrix (Fin m) (Fin n) ℝ), Filter.Tendsto (fun t => a ⬝ᵥ mulVec (t • V) b / t) (𝓝[≠] 0) (𝓝 (innerProductofMatrix (vecMulVec a b) V))-/

    /-m n: ℕ
    a: Fin m → ℝ
    X: Matrix (Fin m) (Fin n) ℝ
    b: Fin n → ℝ
    ⊢ ∀ (V : Matrix (Fin m) (Fin n) ℝ), Filter.Tendsto (fun t => t * a ⬝ᵥ mulVec V b / t) (𝓝[≠] 0) (𝓝 (innerProductofMatrix (vecMulVec a b) V))-/

    /-m n: ℕ
    a: Fin m → ℝ
    X: Matrix (Fin m) (Fin n) ℝ
    b: Fin n → ℝ
    ⊢ ∀ (V : Matrix (Fin m) (Fin n) ℝ), Filter.Tendsto (fun t => t / t * a ⬝ᵥ mulVec V b) (𝓝[≠] 0) (𝓝 (innerProductofMatrix (vecMulVec a b) V))-/

    /-m n: ℕ
    a: Fin m → ℝ
    X: Matrix (Fin m) (Fin n) ℝ
    b: Fin n → ℝ
    V: Matrix (Fin m) (Fin n) ℝ
    ⊢ Filter.Tendsto (fun t => t / t * a ⬝ᵥ mulVec V b) (𝓝[≠] 0) (𝓝 (innerProductofMatrix (vecMulVec a b) V))-/

    /-m n: ℕ
    a: Fin m → ℝ
    X: Matrix (Fin m) (Fin n) ℝ
    b: Fin n → ℝ
    V: Matrix (Fin m) (Fin n) ℝ
    this: innerProductofMatrix (vecMulVec a b) V = a ⬝ᵥ mulVec V b
    ⊢ Filter.Tendsto (fun t => t / t * a ⬝ᵥ mulVec V b) (𝓝[≠] 0) (𝓝 (innerProductofMatrix (vecMulVec a b) V))-/

    /-m n: ℕ
    a: Fin m → ℝ
    X: Matrix (Fin m) (Fin n) ℝ
    b: Fin n → ℝ
    V: Matrix (Fin m) (Fin n) ℝ
    this: innerProductofMatrix (vecMulVec a b) V = a ⬝ᵥ mulVec V b
    ⊢ Filter.Tendsto (fun t => t / t * a ⬝ᵥ mulVec V b) (𝓝[≠] 0) (𝓝 (a ⬝ᵥ mulVec V b))-/

    /-m n: ℕ
    a: Fin m → ℝ
    X: Matrix (Fin m) (Fin n) ℝ
    b: Fin n → ℝ
    V: Matrix (Fin m) (Fin n) ℝ
    this✝: innerProductofMatrix (vecMulVec a b) V = a ⬝ᵥ mulVec V b
    this: (fun t => t / t * a ⬝ᵥ mulVec V b) =ᶠ[𝓝[≠] 0] fun x => a ⬝ᵥ mulVec V b
    ⊢ Filter.Tendsto (fun t => t / t * a ⬝ᵥ mulVec V b) (𝓝[≠] 0) (𝓝 (a ⬝ᵥ mulVec V b))-/

    /-m n: ℕ
    a: Fin m → ℝ
    X: Matrix (Fin m) (Fin n) ℝ
    b: Fin n → ℝ
    V: Matrix (Fin m) (Fin n) ℝ
    this✝: innerProductofMatrix (vecMulVec a b) V = a ⬝ᵥ mulVec V b
    this: (fun t => t / t * a ⬝ᵥ mulVec V b) =ᶠ[𝓝[≠] 0] fun x => a ⬝ᵥ mulVec V b
    ⊢ Filter.Tendsto (fun x => a ⬝ᵥ mulVec V b) (𝓝[≠] 0) (𝓝 (a ⬝ᵥ mulVec V b))-/

    /-No goals-/

theorem problem_a_1 (a : Fin m → ℝ) (X : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ)
  : HasGateauxDerivAt (f_aXb a b) X (vecMulVec a b) := by
    simp [HasGateauxDerivAt]
    simp [Matrix.add_mulVec]
    simp [Matrix.smul_mulVec_assoc]
    simp [← div_mul_eq_mul_div]
    intro V

    /-m n: ℕ
    a: Fin m → ℝ
    X: Matrix (Fin m) (Fin n) ℝ
    b: Fin n → ℝ
    V: Matrix (Fin m) (Fin n) ℝ
    this: innerProductofMatrix (vecMulVec a b) V = a ⬝ᵥ mulVec V b
    ⊢ Filter.Tendsto (fun t => t / t * a ⬝ᵥ mulVec V b) (𝓝[≠] 0) (𝓝 (innerProductofMatrix (vecMulVec a b) V))-/

    /-m n: ℕ
    a: Fin m → ℝ
    X: Matrix (Fin m) (Fin n) ℝ
    b: Fin n → ℝ
    V: Matrix (Fin m) (Fin n) ℝ
    this✝: innerProductofMatrix (vecMulVec a b) V = a ⬝ᵥ mulVec V b
    this: (fun t => t / t * a ⬝ᵥ mulVec V b) =ᶠ[𝓝[≠] 0] fun x => a ⬝ᵥ mulVec V b
    ⊢ Filter.Tendsto (fun t => t / t * a ⬝ᵥ mulVec V b) (𝓝[≠] 0) (𝓝 (a ⬝ᵥ mulVec V b))-/

    /-m n: ℕ
    a: Fin m → ℝ
    X: Matrix (Fin m) (Fin n) ℝ
    b: Fin n → ℝ
    V: Matrix (Fin m) (Fin n) ℝ
    this✝: innerProductofMatrix (vecMulVec a b) V = a ⬝ᵥ mulVec V b
    this: (fun t => t / t * a ⬝ᵥ mulVec V b) =ᶠ[𝓝[≠] 0] fun x => a ⬝ᵥ mulVec V b
    ⊢ Filter.Tendsto (fun x => a ⬝ᵥ mulVec V b) (𝓝[≠] 0) (𝓝 (a ⬝ᵥ mulVec V b))-/

    /-No goals-/
    sorry


/--proof and state-/

theorem problem_a_2 (a : Fin m → ℝ) (X : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ)
  : HasGateauxDerivAt (f_aXb a b) X (vecMulVec a b) := by
    simp [HasGateauxDerivAt]
    simp [Matrix.add_mulVec]
    simp [Matrix.smul_mulVec_assoc]
    simp [← div_mul_eq_mul_div]
    intro V
    have : innerProductofMatrix (vecMulVec a b) V = a ⬝ᵥ mulVec V b := by
      sorry

    have : (fun t => t / t * a ⬝ᵥ mulVec V b) =ᶠ[𝓝[≠] 0] (fun _ => a ⬝ᵥ mulVec V b) := by
      sorry
    /-m n: ℕ
    a: Fin m → ℝ
    X: Matrix (Fin m) (Fin n) ℝ
    b: Fin n → ℝ
    V: Matrix (Fin m) (Fin n) ℝ
    this✝: innerProductofMatrix (vecMulVec a b) V = a ⬝ᵥ mulVec V b
    this: (fun t => t / t * a ⬝ᵥ mulVec V b) =ᶠ[𝓝[≠] 0] fun x => a ⬝ᵥ mulVec V b
    ⊢ Filter.Tendsto (fun t => t / t * a ⬝ᵥ mulVec V b) (𝓝[≠] 0) (𝓝 (a ⬝ᵥ mulVec V b))-/

    /-m n: ℕ
    a: Fin m → ℝ
    X: Matrix (Fin m) (Fin n) ℝ
    b: Fin n → ℝ
    V: Matrix (Fin m) (Fin n) ℝ
    this✝: innerProductofMatrix (vecMulVec a b) V = a ⬝ᵥ mulVec V b
    this: (fun t => t / t * a ⬝ᵥ mulVec V b) =ᶠ[𝓝[≠] 0] fun x => a ⬝ᵥ mulVec V b
    ⊢ Filter.Tendsto (fun x => a ⬝ᵥ mulVec V b) (𝓝[≠] 0) (𝓝 (a ⬝ᵥ mulVec V b))-/
    sorry
    /-No goals-/


theorem problem_a_state (a : Fin m → ℝ) (X : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ)
  : HasGateauxDerivAt (f_aXb a b) X (vecMulVec a b) := by
    simp [HasGateauxDerivAt]
    sorry
    /-m n: ℕ
    a: Fin m → ℝ
    X: Matrix (Fin m) (Fin n) ℝ
    b: Fin n → ℝ
    ⊢ ∀ (V : Matrix (Fin m) (Fin n) ℝ), Filter.Tendsto (fun t => t / t * a ⬝ᵥ mulVec V b) (𝓝[≠] 0) (𝓝 (innerProductofMatrix (vecMulVec a b) V))-/

    /-m n: ℕ
    a: Fin m → ℝ
    X: Matrix (Fin m) (Fin n) ℝ
    b: Fin n → ℝ
    V: Matrix (Fin m) (Fin n) ℝ
    this✝: innerProductofMatrix (vecMulVec a b) V = a ⬝ᵥ mulVec V b
    this: (fun t => t / t * a ⬝ᵥ mulVec V b) =ᶠ[𝓝[≠] 0] fun x => a ⬝ᵥ mulVec V b
    ⊢ Filter.Tendsto (fun t => t / t * a ⬝ᵥ mulVec V b) (𝓝[≠] 0) (𝓝 (a ⬝ᵥ mulVec V b))-/

    /-m n: ℕ
    a: Fin m → ℝ
    X: Matrix (Fin m) (Fin n) ℝ
    b: Fin n → ℝ
    V: Matrix (Fin m) (Fin n) ℝ
    this✝: innerProductofMatrix (vecMulVec a b) V = a ⬝ᵥ mulVec V b
    this: (fun t => t / t * a ⬝ᵥ mulVec V b) =ᶠ[𝓝[≠] 0] fun x => a ⬝ᵥ mulVec V b
    ⊢ Filter.Tendsto (fun x => a ⬝ᵥ mulVec V b) (𝓝[≠] 0) (𝓝 (a ⬝ᵥ mulVec V b))-/
    sorry
    /-No goals-/
