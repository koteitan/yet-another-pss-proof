# kimina-lean-server の使い方（本リポジトリ向け）

YAPSS の Lean 4 証明（`lean/YAPSS/*.lean`）をサーバ経由で大量・並列にチェックするための
[kimina-lean-server](https://github.com/project-numina/kimina-lean-server) の運用メモ。
主にサブエージェントから Lean snippet を検証する用途で使う。

> **バージョン管理の鉄則（このファイルにも適用）**
> - **credential（API キー等）・絶対パス・IP アドレスをコミットしない。**
> - マシン固有の値はすべて kimina-lean-server リポジトリの `.env` に置く（`.env` は
>   そちらの `.gitignore` 済み）。本マニュアルでは絶対パスは `<...>` のプレースホルダ、
>   ホストは `localhost` で記述する。

## 0. 配置（前提）

ワークスペース直下に 2 つのリポジトリが並んでいる:

```
<workspace>/
├── git/                 ← 本リポジトリ（YAPSS。Lean プロジェクトは git/lean）
└── kimina-lean-server/  ← 別リポジトリ（サーバ本体。独自 .git / .env を持つ）
```

## 1. 事前準備（初回のみ）

`kimina-lean-server/` で:

```sh
bash setup.sh          # elan + Lean + repl ビルド（repl/.lake/build/bin/repl ができる）
# .venv と依存は既に用意済みなら不要
```

YAPSS 側 Lean プロジェクトは事前に **ビルド済み**にしておく（REPL が依存をロードできる）:

```sh
cd <workspace>/git/lean && lake build
```

REPL の Lean バージョンと YAPSS プロジェクトの toolchain を一致させること（現在 `v4.30.0`）。

## 2. 設定（`.env`、コミット禁止）

`kimina-lean-server/.env` に以下を設定する。**ここに置く値はすべてマシン固有**で、
絶対パスや API キーを含むため**絶対にバージョン管理に入れない**（`.env` は gitignore 済み）。

```ini
# ホストは localhost のみにバインドする（重要・後述のセキュリティ参照）
LEAN_SERVER_HOST=localhost
# 8000 / 8080 は使わない（他アプリと衝突しやすい）。例として 8123 を使う。
LEAN_SERVER_PORT=8123

# REPL がロードする Lean プロジェクト = YAPSS。絶対パスで指定（このマシンの実体に合わせる）。
LEAN_SERVER_PROJECT_DIR=<ABSOLUTE_PATH_TO>/git/lean
# repl バイナリの絶対パス（setup.sh が作ったもの）
LEAN_SERVER_REPL_PATH=<ABSOLUTE_PATH_TO>/kimina-lean-server/repl/.lake/build/bin/repl

# 認証が必要なら設定（値はコミットしない）
# LEAN_SERVER_API_KEY=<secret>
```

> **よくある落とし穴**: `LEAN_SERVER_PROJECT_DIR` が実体と違う（リポジトリを移動した等）と、
> 起動はするが検証時に `{"detail":"Failed to start REPL"}` / ログに
> `FileNotFoundError: ... /git/lean` が出る。`.env` の絶対パスを今のマシンの実体に直す。

`.env` を直接編集できない／一時的に上書きしたい場合は、環境変数が `.env` より優先されるので
起動時に前置きできる（パスはコミット対象外のシェル上のみ）:

```sh
LEAN_SERVER_PORT=8123 LEAN_SERVER_HOST=localhost \
LEAN_SERVER_PROJECT_DIR=<ABSOLUTE_PATH_TO>/git/lean \
LEAN_SERVER_REPL_PATH=<ABSOLUTE_PATH_TO>/kimina-lean-server/repl/.lake/build/bin/repl \
  .venv/bin/python -m server
```

## 3. 起動

`kimina-lean-server/` で:

```sh
nohup .venv/bin/python -m server > /tmp/kimina-server.log 2>&1 &
```

起動確認はログで（`Uvicorn running on http://localhost:<PORT>` と
`Application startup complete.` が出れば OK）:

```sh
tail -f /tmp/kimina-server.log
```

## 4. ヘルスチェック

エンドポイントは `POST /api/check`、ボディは `{"snippets":[{"id":..,"code":..}]}`。

```sh
curl -s --request POST --url http://localhost:8123/api/check \
  --header 'Content-Type: application/json' \
  --data '{"snippets":[{"id":"t1","code":"#check Nat"}]}'
```

`Nat : Type` が返れば基本動作 OK。YASS プロジェクトのロード確認:

```sh
curl -s --request POST --url http://localhost:8123/api/check \
  --header 'Content-Type: application/json' \
  --data '{"snippets":[{"id":"t2","code":"import YAPSS.Nrm\n#check @YAPSS.psi_proj_notmem"}]}'
```

補題のシグネチャが返ればプロジェクト連携 OK。

## 5. サブエージェント／クライアントからの利用

- `KiminaClient` の既定は `http://localhost:8000` なので、**base_url を本サーバのポートに合わせる**:

  ```python
  from kimina_client import KiminaClient
  client = KiminaClient(base_url="http://localhost:8123")   # API キーがあれば併せて指定
  client.check("import YAPSS.Nrm\n#check @YAPSS.psi_proj_notmem")
  ```

- YAPSS の補題を検証する snippet は先頭に `import YAPSS.<Module>`（例: `YAPSS.Nrm`,
  `YAPSS.Otembed`, `YAPSS.Buchholz17`）を付ける。モジュール名は依存を満たすものを選ぶ
  （例: `CW_of_collapseCanon` は `YAPSS.Buchholz17`）。

## 6. 停止

```sh
# 起動時に表示された PID、または:
pkill -f "python -m server"
```

（プロセスは慎重に。複数エージェントが動いている場合は PID を確認してから kill する。）

## 7. セキュリティ注意

- 本サーバは **任意の Lean コードを実行する REPL** を公開する。`LEAN_SERVER_HOST` は
  `localhost` のみにし、`0.0.0.0`（全インターフェース）にはバインドしない
  （同一マシンのサブエージェントには localhost で十分）。
- `.env`（credential・絶対パス）と起動ログ（絶対パス・PID を含む）は
  **バージョン管理に入れない**。本マニュアルにも実値は書かない。
