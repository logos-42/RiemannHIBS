# Wiki 日志

| 日期 | 类型 | 内容 |
|------|------|------|
| 2026-08-25 | init | 初始化知识系统: bootstrap v2 (LLM Wiki 范式), 8 页面 + manifests + 校验脚本 |
| 2026-08-25 | research | 包络结构: 临界线卷成圆 ‖w‖=√e (criticalLine_circle), expZeta, 桥定理, 多圈叶/折叠, Möbius 随机性; 数值验证 E1-E4 + 10 图 + 螺旋动画 |
| 2026-08-25 | research | 半径叶与缠绕: log(√e)=1/2, 临界叶上每项模长锁定 n^{-1/2} (长度维度锁定), 缠绕圈数 log(n+1), 绝对收敛分界 r>e, 临界叶不绝对收敛 (radius_leaf 方向, Analytic.lean §11) |
| 2026-08-25 | feat | 目标达成: ZetaCoverIsomorphism 结构 (覆盖↔复平面同构, 全由已证定理构成, 无 sorry) + helix_continuation 螺旋延续 (§12); 机制完备环 A⟹B⟹C⟹D⟹A 四方向全证 (§13, A 圆外无零点 / B 零点在圆上 / C 包络半径锁定 ‖e^s‖=√e / D 经典 RH, 输入 h0: 0<Re s) |
| 2026-08-25 | research | 无限多个零点 (§15): 平凡零点无限多已证 (infinitely_many_trivial_zeros, 单射嵌入 n↦−2(n+1)); 非平凡部分如实标注边界 (Hadamard 1893 需增长阶+因子分解/幅角原理, 已有机理不携带 ζ 增长行为) |
| 2026-08-25 | research | 零点分布规律 (§14): 修正两跳跃 — 圆外远处无零点已证 (Re≥1 欧拉乘积, mathlib), 负侧无零点 (函数方程反射), 非平凡零点 ⟹ 0<Re<1 ⟹ 圆环 1<‖e^s‖<e 内; 临界叶√e 是圆环几何平均正中 |
| 2026-08-25 | feat | 隐数坐标系幅角原理 (§16, 局部版): argumentPrinciple_single_zero (∮dz/(z−w)=2πi 单零点原子) + envelope_circle_param (圆参数化) + phase_winding_equals_zero_count (相位缠绕=零点数) + zeroCount_normalized ((2πi)⁻¹∮=1); 诚实标注: 幅角原理为"电路"缺"电源", 无限零点仍赖增长估计输入 |
| 2026-08-25 | research | 无限幅角原理的增长分解 (§17): zeta_growth_decomposition (ζ=compZ/Γℝ) + gammaR_norm_decomposition (\|Γℝ\|=π^(−Re s/2)·\|Γ(s/2)\|) + gammaR_norm_in_envelope_coords / zeta_norm_in_envelope_coords (隐数坐标精确读法, 纯代数已证); 预言 P1–P3 (Stirling + 完成ζ有界) 明确标注为 mathlib 缺失, 把"增长估计"隔离为唯一待形式化边界 |
| 2026-08-25 | research | 有限相位抵消的组合翻译 (§18): 用户思路 — 不证无限性, 转成"有限个自然数相位能否被有限周期度数抵消". phaseCancelRelation (Σaᵢ·log(nᵢ)∈2πℤ) + phaseCancel_of_exp_one (⟹ exp(i·Σ)=1) + phaseCancel_zero_iff_powProduct_one (抵消回0度 ⟺ Π(n+1)^{aᵢ}=1 ⟺ 整数乘法结构); 路线C框架 periodicCancelWindow (360°周期窗口); 路线B稠密性依赖 log ℚ-无关/超越性, mathlib 未形式化, 如实标注阻塞 |
| 2026-08-25 | direction | 候选讨论: "有限组合的 360° 相位抵消" 作为零点构造入口 — 有限前缀 S_N 与尾误差 R_N 精确配平 ⟹ 零点; 已证支撑 (dirichlet_term_rotating_vector / critical_leaf_norm_locked / zeta_phase_alignment_condition), 诚实边界= 单靠有限 S_N=0 不等价 ζ=0, 需 |R_N| 随 N 无界受控(即 §16/§17 增长输入); 有限相消把无限性沉进尾误差而非消掉, 无限版仍赖增长估计; 记为候选机制待推进 |
| 2026-08-25 | research | 缺口① 笔算推导 (不落码, 先想清): 关键翻转 — `dirichlet_term_rotating_vector` 是复恒等式(与 σ 无关), 故相位/旋转向量机制对任意 Re 成立; 临界带断路在"级数=ζ"而非相位. 正解: 边界带 `ζ(s)=0` = 全纯函数取零(mathlib differentiableAt) — 不需级数和; 隐数语义"对齐零点"=覆盖空间 `expZeta_phase_principal` (ζ̂(w)=ζ(log r+iθ)) 良定等式. 经典桥: Re>0 η 交替 Abel 条件收敛 + 排斥因子 (1−2^{1−s}) 在临界带恒非零 (2^{1−s}=1 仅实部=1, 不在带内) ⟹ ζ=0⟺η=0 在临界带成立. 结论: 缺口① 的真阻碍 = mathlib 缺"条件收敛(η)+Abel/函数方程延拓"工具, 非概念不可能; 建议走覆盖语义"对齐零点"命题 + 临界带诚实标注. 缺口② 保持如实(N(T)→∞ 缺增长输入) |
| 2026-08-25 | verify | 缺口①/② 审计 (§10→§14→§17 连通性): 验证确认构建通过 (Analytic.lean 无 sorry, 仅 ring linter 建议); 缺口① = `zeta_phase_alignment_condition` 限 Re>1 (级数直接=ζ), 临界带 0<Re<1 内 ζ 为解析延拓, "旋转向量和=0" 与 "ζ=0" 无已证桥 (需 η/函数方程/Abel 正规化延拓); 缺口② = "N(T)→∞" 依赖 Stirling+完成ζ有界 (P1–P3, mathlib 缺失), 即使完成也只证"无限多"非 RH; 两缺口已写入 current-status 诚实边界 |
| 2026-08-25 | feat | §19 缺口① 桥落地 (代码, 无 sorry 编译通过): eta_term_rotating_vector (η 第 n 项=(−1)^n×旋转向量, 复恒等式, dirichlet_term_rotating_vector 反向 rw+ring) + eta_phase_alignment_condition (Re>1 下 η(s)=0 ⟺ 交错旋转向量和=0, 镜像 §10 换交替符号); 把"相位对齐/抵消"语言与 η 级数接通; 临界带 0<Re<1 的严格对齐需条件收敛 η+Abel/函数方程正则化, mathlib 缺此基建, 如实标注为待形式化 (不装证) |
| 2026-08-25 | feat | §20 隐数对齐零点落地 (代码, 无 sorry 编译通过): alignmentZero (零点的"相位对齐"信息压缩谓词 — s 对齐零点 ⟺ 交错旋转向量(η 形态)和=0) + alignmentZero_iff_zeta_zero (Re>1 桥, 前提排斥因子≠0: alignmentZero s ⟺ riemannZeta s=0, 经 eta_eq_mul_zeta); 把既有零点重述为相位结构显式化, 非发明独立对象. 诚实标注: 无限非平凡零点仍是独立边界(需条件收敛 η+Abel/函数方程(§19) + 增长输入(§16/17)), 未装证 |
