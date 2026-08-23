# RiemannHIBS — 隐数运算法则 × 黎曼 ζ/η 函数构造

**Lean 4 形式化**：用 HIBS（Hidden-space Bridge System）理论中的**隐数运算法则**，
构造黎曼猜想中的核心函数 —— **Riemann ζ 函数**与 **Dirichlet η 函数** ——
并证明其代数骨架。

纯 core Lean 4（v4.28.0，无 mathlib），值类型用 `Int`。

**English version**: [README.md](README.md)

---

## 1. 思路：隐数、隐虚数、隐方数如何承载 ζ 与 η

HIBS 的隐数 `⟨值, 标签⟩` 有两条核心流规则：

| 法则 | 内容 | 标签 |
|------|------|------|
| A2a | 加/减留在隐层 | `S` |
| A2b | 乘法强制流向实部 | `R` |
| A3  | 开方强制流向虚部 | `iR` |

三个隐数组件在黎曼描写中各司其职：

| 组件 | 定义 | 流规则 | 在 ζ/η 描写中的角色 |
|------|------|--------|---------------------|
| **隐数** | `Hidden` = ⟨val : Int, tag⟩ | A2a 加减留隐层 | ζ/η 部分和是隐数——加法封闭使级数留在隐层 |
| **隐虚数** | `hiddenImag b` = ⟨b, iR⟩ | A3 开方流入虚部 | 临界线点 1/2 + it 的虚部 t 承载于 iR 支（`doubledEmbedding`） |
| **隐方数** | `hSqrt h` = ⟨h.val, iR⟩ | A3 开方强制投影到 iℝ | 平方量 t² 经 √ 流入 iR 支，投影为纯虚数 ⟨0, t²⟩（`sqrt_pure_imag`）——虚轴方向从隐方数涌现 |

> **上游注记（2026-08-21）**：HIBS（Lean_HIBS）自 commit `cc08ceb` 起大幅重构 ——
> `Definitions.lean` 新增 ℂ 的 `Add`/`Mul` 实例、`conj`、`CompositeHidden`、`DecidableEq`
> 等；`Axioms.lean` 改为参数化结构 `Axiom1/2/3` + `HIBS_Axioms`；并新增
> `Conjugation`（conjS/signalRev）、`Sqrt`（符号感知 `hSqrtFull`）、`Derivation`
> （`hEval`/`imul`/`hMulAdj`）、`Embedding`（ι'/π'）、`Model`（公理独立性 M₁/M₂/M₃）
> 五个模块。本仓库的 `Hidden.lean`/`Axioms.lean` 已**对齐新版 Definitions/Axioms**
> （`ι_R` 替代旧 `hiddenProj`，`CompositeHidden`/`π'` 移到 Hidden.lean），ζ/η 构造不变。
>
> 关于开方符号：HIBS 论文模型 (4.5) 与例 4.3 曾有一处符号笔误，几何一致约定为
> **⟨+ ↦ iR⁻、⟨− ↦ iR⁺**，已由 `cc08ceb` 修正。本仓库 `hSqrt` 为简化的
> 值保持标签模型（无半轴结构，对应 A3 标签子句而非 (4.5) 值公式），**不受影响**；
> 完整 A3（符号感知 `hSqrtFull`）在 Lean_HIBS `HIBS/Sqrt.lean`。

对应表：

| 隐数对象 | 运算法则 | 标签 | 数学对象 |
|----------|----------|------|----------|
| `zetaTerm w n = ι_R (w n)` | A2b 乘法投影 | `R` | n^(−s) 项（幂 = 多次乘法） |
| `zetaSum w N`（逐项 hAdd） | A2a 加法封闭 | `S` | ζ 部分和 |
| `etaSum w N`（交错符号） | A2a 加法封闭 | `S` | η 部分和 |
| `geomH p e`（几何因子） | A2a 加法封闭 | `S` | 1 + p + … + p^e |
| `hMul (geomH p a) (geomH q b)` | A2b 乘法投影 | `R` | 欧拉乘积因子（乘积强制投影） |
| `smoothH p q a b`（网格和） | A2a 加法封闭 | `S` | {p,q} 生成整数上的 ζ 和 |
| `doubledEmbedding t`（双分量嵌入） | — | `S`/`iR` | 临界线 2s = 1 + 2it 的整数坐标表示 |
| `hSqrt` 作用于 t² | A3 | `iR` | 虚数方向从隐方数涌现 |

---

## 2. 已证定理（全部通过 Lean 4 验证）

### 隐数运算法则（Hidden.lean）
- `hiddenArithmetic_holds` — A2a ∧ A2b ∧ A3 在该模型成立
- `add_flow_S / sub_flow_S / mul_flow_R / sqrt_flow_iR` — 四条流规则
- `π_nonInjective` — 投影非单射（A1）：不同隐数可投影到同一可观测值
- `CompositeHidden` / `π'` — 双分量嵌入与投影（对齐上游 Thm 6.5 的 ι'/π'）

### 三公理形式化（Axioms.lean，对齐新版 HIBS）
- `axiom1_holds` — (A1)：projR/projImag 均非单射
- `axiom2_holds` — (A2)：± 留 S 支，× 强制投影 R 支
- `axiom3_holds` — (A3)：√ 强制投影 iR 支
- `all_axioms_hold` — 三公理在标签对模型 S = ℤ×{S,R,iR} 上全部成立

### ζ/η 构造（Zeta.lean）
- `zetaTerm_tag_R` — 每一项是 R 支（乘法强制投影）
- `zetaSum_tag_S / etaSum_tag_S` — 部分和留在隐层 S 支（加法封闭）
- `zetaSum_val / etaSum_val` — 部分和的值 = 项值之和
- `zetaSum_observable` — π(ζ 部分和) = ⟨和, 0⟩

### 解析延拓骨架（Zeta.lean）★
```
eta_reconstructs_zeta :  (etaSum w (2M)).val = (zetaSum w (2M)).val − 2·evenSum w M
zeta_from_eta        :  (zetaSum w (2M)).val = (etaSum w (2M)).val + 2·evenSum w M
```
这是经典恒等式 **η(s) = (1 − 2^(1−s))·ζ(s)** 的有限代数骨架：
偶数项之和 = Σ(2k)^(−s) = 2^(−s)·ζ，故 `2·Σ(偶数项) = 2^(1−s)·ζ`。
权重 `w : Nat → Int` 象征 `n^(−s)`；无限级数收敛与解析延拓是草案声明。

### 欧拉乘积（Euler.lean）
- `euler_product_expansion` — **生成定理**：∏_p(1 + p + … + p^a) = Σ_{p^i q^j} p^i q^j
  （"所有质数相乘，生成所有整数"的有限形式，任意 p, q, a, b 成立）
- `euler_product_tag_R` — 欧拉乘积是 R 支（乘法强制投影）
- `geomH_tag_S / smoothH_tag_S` — 几何因子与网格和都是 S 支
- `euler_zeta_observable_bridge` — **隐桥定理**：
  π(欧拉乘积) = π(ζ 部分和)（R 支与 S 支在可观测切片 ℂ 上一致）

### 临界线与隐方数（Riemann.lean）
- `trivialZero` — 平凡零点 s = 2k（负偶数）；实例：−2
- `criticalLine` — Re(s) = 1/2 的整数倍化表述：2·Re(s) = 1
- `doubledEmbedding_observable` — 临界线 2s = 1 + 2it 的隐数嵌入
- `sqrt_pure_imag` — 隐方数把 t² 送入 iR 支，可观测切片为纯虚数 ⟨0, t²⟩

### 解析延拓与隐数空间黎曼猜想（Analytic.lean，mathlib 完整版）★
本模块用 **mathlib 的解析延拓**（`riemannZeta : ℂ → ℂ`，s≠1 处可微，
`zeta_eq_tsum_one_div_nat_add_one_cpow` 给出 Re(s)>1 的 Dirichlet 级数形式，
`riemannZeta_one_sub` 为函数方程）把黎曼猜想提升到隐数空间：

- **隐数 ↔ 复平面双向互推**：`hEval` 把隐数读成复数（⟨x,S⟩↦x、⟨x,R⟩↦−x、⟨x,iR⟩↦xi）；
  `ι'` 把格点 (a,b) 嵌入双分量隐数；`π'_ι'_id` 证明 π'∘ι'=id。投影非单射
  （`π_nonInjective`，公理 A1）。
- **隐数空间中的 ζ**：`zetaHidden h := riemannZeta (hEval h)`。平凡零点存在：
  `zetaHidden_trivialZero`。倍化临界线 2s = 1 + 2it 由 `doubledEmbeddingC t` 嵌入，
  `doubledEmbeddingC_on_line` 证明确实落在临界线上。
- **解析延拓公式（已证，无 sorry）**：`eta_eq_mul_zeta` —
  η(s) = (1 − 2^(1−s))·ζ(s)（Re s > 1），其中 η(s) = ∑' (−1)^n/(n+1)^s 为
  Dirichlet eta 级数（经 `tsum_even_add_odd` 奇偶拆分；
  `evenSum_eq_mul_zeta` 证偶数项 = 2^(−s)·ζ）。这是 Zeta.lean 有限骨架
  `eta_reconstructs_zeta` 的解析完整版。
- **隐数空间黎曼猜想**（声明，非 sorry — 与 mathlib 自己的 `RiemannHypothesis`
  一致）：每个可观测值为延拓后 ζ 非平凡零点的隐数，其实部 = 1/2：
  `RiemannHypothesisHidden`。定理 `riemannHypothesis_hidden_of_mathlib`：
  经典猜想成立 ⟹ 隐数版成立。

### 包络结构：expZeta 与临界线圆周（Analytic.lean 第 6 节）★
隐数三标签就是复平面的锚定方向——hEval 读作 ⟨x,S⟩↦x、⟨x,R⟩↦−x、⟨x,iR⟩↦x·i，
即 x·e^{iθ}，θ ∈ {0, π/2, π}。把标签连续化（θ ∈ S¹）+ 值连续化（x ∈ ℝ）后，
隐数空间包络成极坐标/复对数曲面 w = log z（螺旋柱面 / 万有覆盖）。在包络坐标
w = e^s 下，临界线卷成一个圆周：

- `expZeta w := riemannZeta (Complex.log w)` — ζ 拉回到包络坐标（主支，
  w ∉ (−∞, 0]）
- `envelopeRadius : ℝ := Real.sqrt (Real.exp 1)` — 包络半径 √e
- `criticalLine_circle (t : ℝ)`（已证，无 sorry）— 对任意 t，‖exp(1/2 + it)‖ = √e：
  临界线 Re s = 1/2 的像 = 圆周 |w| = √e。证明：exp(1/2+it) = exp(1/2)·exp(it)，
  其中 ‖exp(it)‖ = 1（`norm_exp_ofReal_mul_I`），exp(1/2) = √e
  （`exp_half_eq_sqrt_exp_one`）
- `zero_on_critical_line_envelope` — 临界线上的零点 ζ(1/2+it)=0 映射到圆周
  |w| = √e 上的点。**RH ⟺ 所有非平凡零点共圆 |w| = √e。**（几何画像：极点
  s=1 → 单点 w=e；平凡零点 → 点列 e^{−2k}→0；收敛半平面 → 圆外 |w|>e；
  η 因子多余零点 s = 1+2πik/ln2 → 稠密于 |w| = e，因 2π/ln2 无理。）

数值验证：`experiments/envelope.py`（E1 零点共圆 √e；E2 η 多余零点稠密于
|w|=e；E3 平凡零点点列→0；E4 ζ'/ζ 沿矩形绕数 = 零点数——数圈数 = 数零点）。

### 相位包络 ↔ 对数坐标（Analytic.lean 第 7-8 节）★
把 EnvelopeC 的相位包络与 expZeta 共圆图景接通：

- **桥（§7）**：`criticalPhaseC_envelope_circle (t : ℝ)`（已证，无 sorry）—
  ‖exp(hEvalPhase (criticalPhaseC t))‖ = √e：相位包络的临界截面映射到圆周
  |w| = √e。`zero_envelope_circle`：临界线上的 RH 零点 ⟹ 像共圆。
- **主支相位参数化（§8）**：`expZeta_phase_principal` — 对 r > 0，
  θ ∈ (−π, π]：ζ̂(r·e^{iθ}) = ζ(log r + iθ)，即 expZeta 在相位坐标下就是
  ζ 的对数坐标（log 主支覆盖 ℂ∖(−∞,0]，相位叶 θ ∈ (−π,π] 恰好覆盖该区域）。
- **多圈叶（§8）**：`phase_periodic`（归纳）— 叶 ⟨r, θ+2πk⟩ 对任意 k 投影
  回同一点；`phase_fold_neg_axis` — 所有叶 π+2πk 折叠到负实轴 −r（离散折叠
  `envelope_fold` 的连续版）；`phase_fold_many_sheets` — 可数多叶共享同一
  可观测值；`envelope_universal_cover_branch` — 每个 w ≠ 0 的每一圈 k 都有
  主支相位原像。合起来：相位包络是 ℂ∖{0} 上的可数叶覆盖（万有覆盖的离散骨架）。
- **Draft（如实标注）**：`EnvelopeUniversalCoverMultiLog` — 多值 log 的叶
  分支 log w + 2πik 需要多值 arg；mathlib 的 Complex.log 是单值主支（把所有
  叶折叠回主值），完整叶展开超出本模块范围。

图：`viz/fig5_rollup.png`（临界线直线 ↔ 圆周 |w|=√e，零点编号对应）与
`viz/fig6_winding.png`（argument principle：像曲线绕原点 6 圈）—
  见 `viz/envelope_extra.py`。

---

## 3. 草案声明（未证明 — 如实标注）

以下内容依赖实数系上的级数收敛、解析延拓与函数方程，超出 core-Lean 整数模型，
以 `structure` 形式声明（字段永不被当作证明）：

- `RiemannHypothesis` — 所有非平凡零点都在临界线 Re(s) = 1/2 上
- `HilbertPolya` — 非平凡零点的虚部构成某自伴算符的谱

---

## 4. 构建与运行

```bash
cd RiemannHIBS
lake build
.lake/build/bin/riemannhibs
```

依赖：core 模块（`Hidden`/`Axioms`/`Zeta`/`Euler`/`Riemann`）用纯 core Lean 4
（无 mathlib）。`Analytic` 模块（解析延拓、隐数空间黎曼猜想）需要
**mathlib v4.28.0**（见 `lakefile.toml`；本地 git 路径复用已有 mathlib 克隆——
可改为你自己的 mathlib checkout 或 `https://github.com/leanprover-community/mathlib4.git`）。
检查无 `sorry`：

```bash
grep -rn -- "sorry" RiemannHIBS/ Main.lean
```

---

## 5. 局限与后续

- 值类型为 `Int`：`ζ(2) = π²/6` 等超越结果、级数收敛、解析延拓需要 ℝ/ℂ 分析
  （可引入 mathlib 后继续）。
- 完整黎曼猜想（无限多个零点全在临界线）是开放问题，本项目的价值在
  **构造层**：隐数运算法则为 ζ/η 的级数结构提供了精确的代数骨架，
  并让"欧拉乘积 = ζ 和式"这一质数-整数桥以可验证的形式落地。

---

## 6. 参考

- Liu & Xu, *The Hidden-space Bridge System*（HIBS 三公理）—
  现有形式化见 [**logos-42/Lean_HIBS**](https://github.com/logos-42/Lean_HIBS)
- 基于这些公理的物理纲领：
  [**logos-42/Hibs-Physics**](https://github.com/logos-42/Hibs-Physics)
  （代数涌现物理：表示完备性、核零定理）
- Riemann, *Ueber die Anzahl der Primzahlen unter einer gegebenen Grösse* (1859)
- **English README**: [README.md](README.md)
