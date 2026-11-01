# 形式化工作流（L20261018 ch.3–4 项目复用版）

> 本文件只收**可复用且不陈旧**的经验：每条都写成「触发条件 → 动作 → 判据」，
> 并尽量给出实弹出处。**不写**本轮状态、不写"还剩什么"（那些会立刻过期）。
> 适用对象：把一篇数学论文的若干章节形式化进 Lean 4 + mathlib 的项目。

---

## 0 三条不可省的前置

| # | 动作 | 判据 |
|---|---|---|
| **P1** | **外部侦察先行**：任何「mathlib／本地库没有 X」的判决之前，必须按**内容式关键词**（不是名字）检索：mathlib master、本地 pin，以及本地大快照（本仓：`raw/TauCeti`、`raw/fermats-last-theorem`、`raw/openai-math-formalized-algebra` 等） | 判决须记录**搜过的目录 + 命中清单 + 版本（pin 与 master）**。否则该判决作废 |
| **P2** | **侦察命中要落成机检件**：把找到的库内件**在本项目载体上实例化**并编译 | 只写进 Markdown ＝ 未落盘；下一轮必然重做 |
| **P3** | **不继承缺口清单**：上一轮/交接件里写的「只剩 X」不是事实来源 | 开工第一件事：`grep -rn "<结论关键词>"` 重新生成缺口清单，并核对**最终件**的假设画像 |

**为什么 P1–P3 是硬要求**：本项目的最大单项浪费全部来自「把『我没搜到』读成『不存在』」
与「照抄过期清单」。实弹：
`MvPolynomial`×`IsLocalization` 的桥**早就在** `Mathlib/RingTheory/MvPolynomial/Localization.lean:42`，
而在 `Mathlib/Algebra/MvPolynomial/` 里连搜三轮全负 ⟹ 自建三轮失败；
`Nat.card ↥(zmultiples x) = addOrderOf x` 的真名是 `Nat.card_zmultiples`（不在 `AddSubgroup.` 下），
猜 12 个名字全负后误判「mathlib 无」。

---

## 1 选靶：先判「哪条是路线的障碍」，再判「可不可做」

1. **数假设要数在最终件上。** 同一结论常有**多条路线**，中间件的假设画像≠结论的口径。
   本项目实弹：第 4 章的一般 Hensel 版本（`Hyp289`）**零** `IsNonarchimedeanLocalField`，
   而我据「自己正在走的那条 §2 路线」的中间件断言「一般情形需要重定义惯性」——**错**。
   **判据**：`grep -c "<该假设>" <最终件>.lean` ＋ 先读项目的**规范件注册表**（本仓 `PROOF-MAP` §3）。
2. **判「假设能否去掉」前，先看它是否出现在 `def` 的 binder／`def` 体里。**
   - 出现在**定义**里 ⟹ **不是假设松弛，是定义重建**；
   - 只出现在**定理**里 ⟹ 才可能是松弛。
   本项目实弹：`inertiaLoc` → `maximalUnramifiedExtension` → `unramifiedExtension` 的 **`def` 体**里是
   `Nat.card 𝓀[K]`，而 `Finite 𝓀[K]` 只由 `IsNonarchimedeanLocalField` 供给
   ⟹ 去完备性会让三个定义**同时失去意义**。
3. **「任两元相关」≻ 维数理论。** 证「某子空间上线性映射单射」时，先用「任意两元素线性相关」
   形态（常**零假设**），不要先上 `finrank`（那要 `FiniteDimensional`，而它可能**不是**论文假设）。
   本项目实弹：`finrank_VKG_eq_one` 要走 `[FiniteDimensional]` ＋ 杯积非退化性（两条都非论文假设）；
   而 `ker_dependent`（「`ker v̄` 内任两元相关」）零假设 ⟹ 两条机器假设同时消失。

---

## 2 写证明：Lean 侧的「假卡住」四型（报错点不在数学）

| 症状 | 修法 |
|---|---|
| 报错里出现**编号 metavar**（`?m`／`?m.16`）在实例的参数位置（如 `IsGalois ?m.16 L`） | 隐式类型参数在语句里留了 metavar。**显式写 `(K := K) (L := L)`** |
| 实例搜索卡在「某表达式上的类型参数」 | 把该参数显式化：`IsLocallyConstant (X := …) (f x)` |
| `rw` 报「找不到 pattern」而**显示上一样** | 同一个 `•` 有多种精化形状（`↑↑γ`／`γ.toLinearMap`／`↑γ`）；把引理**按目标里的形状**陈述。或目标里有 **beta-redex**（structure literal 未归约）⟹ 补一条 `:= rfl` 的取值引理再 `rw` |
| 「结构同构的 `Subsingleton` 转移」`haveI` 无效 | 实例路径不同 ⟹ 直接 `@Subsingleton.elim _ hZ a b` |
| `failed to synthesize SMulZeroClass R M` 而 `Module R M` 好使 | 该类型上 `smul_zero`/`smul_eq_zero` 不可用 ⟹ 把标量代数**搬到定义域**做（`Submodule.smul_mem` ＋ `LinearMap.mem_ker`） |
| `Unknown identifier q` / `Invalid argument name` | **只在证明里用到的变量不会成为参数**（结论里不出现 ⟹ 不泛化）。把 `(q : ℕ) [Fact q.Prime] … (h : p.Coprime q)` **显式写进签名** |
| 大签名引理报参数错位 | 先 `#check @lem` 打**全签名**，再按打印顺序用**具名参数** |
| `expected token` 且行内只有标识符 | 非 ASCII binder 名（`ȳ`／`π₀`）⟹ 先改 ASCII |

**循环禁令**：同一处错误连试 3 次不成，**停下写根因假设**并做最小复现，禁换写法盲试。

---

## 3 装配：让「引理」和「结论」都变成构造

1. **先把要消去的假设写成 `∃`（或 `def`）**，再用库内定理把它**构造**出来；
   装配时只搬 `d := F5 ∘ ∂²` 这类一行。
2. **符号由定义吸收。** 需要 `−y` 而手上是 `y`，就让自由参数取 `−F5∘∂²`，不要在结论里改符号。
3. **`Prop` 槽的差异由证明无关性吸收**：装配时先看槽是不是 `Prop`；是就直接写目标形态，
   不要先上 `map_congr_of_hom_apply`。
4. **`rfl` 级取值引理**：凡 `def` 的 `toFun` 是 lambda，而下游要 `rw`，先加
   `theorem f_apply … := rfl`（`rfl` 会做 beta）。
5. **写出「三级口径」**：同一章常有「一般载体／论文级（吃某个具名假设）／无条件」三档。
   **在 README 与报告里必须分开列**，否则「检验通过」会被误读。本项目实弹：
   第 4 章曾有 `ch4`（吃 `d`）与 `ch4u`（`d` 被构造）两组，只列 `ch4` 就是误导。

---

## 4 验证：只信官方 comparator，且要「判据自证」

1. **验证用官方工具**（本项目 `comparator` v4.35.0 ＋ `lean4export` v4.35.0）。
   驱动脚本只做三件事：建 olean 搜索路径、把定理**语句**克隆成 `Challenge`（证明 `sorry`）与
   `Solution`（项目自己的证明项）、写 `config.json`；**判定由官方二进制做**。
2. **工具本身要有判别力自证**：正例（正确的解被判过）＋ **负例**（语句不符被拒、非法公理被拒）。
   本项目的 `validate-comparator-tools.sh` 就是这张表；**没跑过它，阴性读数不取用**。
3. **`permitted_axioms` 写死三条**（`propext`／`Quot.sound`／`Classical.choice`），
   外加项目侧的 `#print axioms` 与 `sorry` 审计做交叉。
4. **「无条件」必须逐件核**：对每个目标 `#check @名` 的**完整签名**扫描被消去的假设名，
   并放一条**正例**（已知吃该假设的旧件必须被抓出来）。本项目：`clean=16 flagged=1`，
   flagged 的正是正例对照。

---

## 5 交付：仓库要像「库」，不像「战役工作区」

1. **源码自足**：依赖（本项目 TauCeti 子集）vendored，mathlib 用 pin；读者 `lake exe cache get && ./run-comparator.sh` 即可。
2. **`globs` 与根模块同在或同不在**：没有根模块 `X.lean` 时写 `["X.+"]`（写裸 `"X"` 会让 Lake 找不存在的
   根模块而报 `no such file or directory`）；**一旦加了根模块 `X.lean`**，必须写 `["X", "X.+"]`——否则根模块
   不是构建目标，而任何 `import X` 都会报 `object file 'X.olean' does not exist`（本项目实弹：`ch3u` 组
   一直红，正是因为根模块从未存在）。
3. **import 前缀必须与库名一致**：`lean_lib L20261018` ⟹ 模块名 `L20261018.Foo`，文件里写 `import Foo` 解析不了。
4. **闭包用 `public import` 也算**：只匹配 `^import` 会静默漏掉 vendored 依赖（本项目漏了 53 个 TauCeti 模块）。
5. **拆脚手架**：探针／`Check*`／台账／计划／日志一律不进交付仓库；
   交付仓库只留 `结果 + 依赖 + 验证 + README + LICENSE`。
6. **README 短**：三段——怎么验、验的是什么、哪几档口径。读者不需要工具的原理科普。
7. **库形态：重命名安全，合并不安全。** 战役工作区的 `HypNNN.lean` 是「可编译但不可检索」的形态：
   文件名不携带内容，GitHub 的目录浏览与文件名检索双双失效。迁移分两条路，风险差一个量级：
   * **重命名（含改目录）= 零语义风险**：改的是*模块名*，`import` 之外的每一行都逐字不变 ⟹
     名字解析、`open` 作用域、`namespace` 栈全都不动。**判据**：迁移后
     `(declaration, line)` 多重集**逐条不变**（改名不改数、不改行）——不要拿「声明总数」当判据，
     修一次索引器的正则就会让它变。
   * **合并 = 高语义风险**：拼接改变 `open`／`namespace` 的上下文与候选集，`GaloBase.cup` 这类
     二级名会解析到别处而报 `Unknown identifier`（本项目实弹，整轮报废）。合并必须逐段重放
     `open`／`set_option` 并逐批 `lake build`。
   **文件名必须是合法的标识符分量**：`[A-Za-z0-9_]`，**不得含连字符**（`zz-test-hyphen.lean` 被解析成
   模块 `zz`，`import` 直接坏），**不得以数字开头** ⟹ `Step017_…` 的前缀不是装饰，它让名字成为标识符。
   **根模块的 `/-! … -/` 必须放在 `import` 之后**（`import` 只能在文件最前）。
8. **索引器要能 Ctrl-F**：`DECLARATIONS.md` = `declaration | module | line | paper locator`。
   正则须允许**前置 attribute**（`@[simp] lemma Foo_apply` —— 只认行首关键字的版本会静默漏掉 29 条，
   而那恰好是最常被 grep 的 `_apply` 族）；**匿名 `instance : Foo` 无名字可索引**，只能计数，
   且**必须在表头报出这个数**（本项目 42 条），不许静默丢。
   迁移后 `DECLARATIONS.md` 与代码**同批提交**。

**工艺**：任何脚本写文件，若内容含非 BMP 字符，**先构造内容并 `encode('utf-8')` 校验，再原子替换**；
禁先 `open(path,"w")`（会立即截断，随后异常即静默毁件）。

---

## 6 报告纪律

1. **结论级三态**：`✓-formalized`（build 过／无 `sorry`／axioms 恰三条）｜`✗-refuted`（否定已形式化）｜
   `∅-open`（证不出，**不得读作「否」**）。
2. **能形式化的不用模型审查**；引用外部已发表定理写成**具名假设 ＋ 类型锁定 ＋ 非空见证**即得 `✓` 条件定理。
3. **不许把「清单」当「状态」**：`ASSUMPTIONS.md`／`PROOF-MAP`／历次 `ALIGN-*` 只能当**线索**；
   判假设只认当前签名（含**匿名 `→` 前提**——它们不叫 `h…`，关键词 grep 必漏）。
4. **改过的判据必须跑回归对照**：本项目反自指过滤首版误删合法标题，靠回归当场暴露。
5. **对外文档要么进校验件（镜像＋哈希＋闸门），要么每轮提交**；只存在于工作区的产物改动不可核、损失不可见。

---

## 7 一页速查（开工 → 收口）

```
开工:  ① 读最终件的假设画像（不是自己的路线）  ② 内容式 grep 外部＋本地大快照
       ③ 缺口语义分类：观测数据 vs 确定性定义（后者必须算，不得记为「仍开」）
写证明: 假卡住先查记法／实例（§2 表）；同错误 3 次 ⟹ 写根因 + 最小复现
装配:  被消去的假设写成 ∃/def 并构造；符号由自由参数吸收；Prop 槽免搬运
验证:  官方 comparator + 工具自证（正例＋两条负例）+ 逐件签名扫描（带正例对照）
交付:  源码自足、globs 与根模块同在、import 前缀一致、闭包含 public import、拆脚手架、README 三段
库形态: 只重命名不合并（重命名零语义风险；合并要重放 open）；文件名须合法标识符（禁连字符／首数字）；
       判据 = (declaration, line) 逐条不变；DECLARATIONS.md 带 module+line+paper，且报匿名 instance 数
收口:  build 0 err 0 warn ｜ axioms 恰三条 ｜ comparator 全绿 ｜ commit（含文档）
```
