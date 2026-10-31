import Hyp156

/-!
# R1006：**`D`（符号代数张量积）作为代数对象 —— 第一块：类的可乘性**

长期目标第 (6) 项（`D = (a₁,b₁)_F ⊗ (a₂,b₂)_F` 作代数对象）。**本轮侦察 + 第一块机检**：

**侦察结论（详见 `RECON-D6.md`）**：部件基本都在库 ——
* `SymbolAlg K p a b ζ`（`Hyp47`）＋ `tensorSymbolAlg`（`Hyp49`，张量在 `a_i ∈ K^{×p}` 时分裂）；
* **符号代数的类 = Kummer 杯积类**：`Hyp77.symbolAlg_brauerClass_eq_verbatim`；
* `BrauerGroup.mk_tensorProduct`（TauCeti `Algebra/BrauerGroup/Group.lean:195`）：
  `mk (A ⊗ B) = mk A * mk B`。

**本文件**：`D` 的张量积类可乘性（`Br` 的乘法即张量积），即 `[Sym₁ ⊗ Sym₂] = [Sym₁]·[Sym₂]`。
-/

set_option maxHeartbeats 2000000

open TauCeti

namespace L20261018

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] {ζ : F} (hζ : IsPrimitiveRoot ζ p)

/-- **符号代数张量积的 Brauer 类可乘**：`[Sym(a₁,b₁) ⊗ Sym(a₂,b₂)] = [Sym(a₁,b₁)]·[Sym(a₂,b₂)]`。

这是论文 `D = (a₁,b₁)_F ⊗ (a₂,b₂)_F` 的**对象层**第一步（`Br` 的乘法就是张量积）。 -/
theorem brauerClass_tensorSymbol {a1 b1 a2 b2 : F}
    [Algebra.IsCentral F (SymbolPres.SymbolAlg F p a1 b1 ζ)]
    [IsSimpleRing (SymbolPres.SymbolAlg F p a1 b1 ζ)]
    [FiniteDimensional F (SymbolPres.SymbolAlg F p a1 b1 ζ)]
    [Algebra.IsCentral F (SymbolPres.SymbolAlg F p a2 b2 ζ)]
    [IsSimpleRing (SymbolPres.SymbolAlg F p a2 b2 ζ)]
    [FiniteDimensional F (SymbolPres.SymbolAlg F p a2 b2 ζ)] :
    BrauerGroup.mk (CSA.of F (TensorProduct F
        (SymbolPres.SymbolAlg F p a1 b1 ζ) (SymbolPres.SymbolAlg F p a2 b2 ζ)))
      = BrauerGroup.mk (CSA.of F (SymbolPres.SymbolAlg F p a1 b1 ζ))
        * BrauerGroup.mk (CSA.of F (SymbolPres.SymbolAlg F p a2 b2 ζ)) := by
  rw [← BrauerGroup.mk_tensorProduct]

end L20261018
#print axioms L20261018.brauerClass_tensorSymbol
