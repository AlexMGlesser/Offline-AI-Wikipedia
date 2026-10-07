# Offline AI Wikipedia

Download all of English Wikipedia, organize it on your own drive, and search it with a
local search engine and a local AI librarian. Once set up, everything runs offline on
your own computer.

## What's here

| File | What it does |
|---|---|
| `download_wikipedia.py` | Downloads the latest Wikipedia dumps (and the Kiwix offline reader with images), verifies them, then organizes every article into its own file plus a SQLite catalog of titles, categories and redirects. |
| `librarian.py` | **GLESSER ARCHIVE**: builds a full-text search index, then serves a local search app with ranked results, article reader, categories, a local AI agent chat (via Ollama), an HTTP agent API, and an MCP server. |

Both are single files using only the Python standard library, plus `requests` for downloading.

## Requirements

- Python 3.8+ (with SQLite FTS5, included in python.org and conda builds)
- `pip install -r requirements.txt`
- Disk: about 350 GB for English (downloads, organized copy and search index)
- For the AI agent: [Ollama](https://ollama.com) and a GPU with roughly 8-16 GB VRAM

## Setup

1. **Configure** `download_wikipedia.py` at the top of the file:
   - `DEST`: where to store everything
   - `USER_AGENT`: replace `you@example.com` with your contact email (Wikimedia asks
     automated downloaders to identify themselves; the script won't start without it)
   - `OTHER_LANGUAGES`, `INCLUDE_ENGLISH_ALL_CURRENT_PAGES`: what to download
2. **Download and organize:**
   ```
   python download_wikipedia.py
   ```
   It's resumable: Ctrl+C and rerun to continue. Other modes: `--download-only`,
   `--organize-only`, `--lookup "Title"`, `--category "Name"`.
3. **Build the search index** (one time; set `DATA_DIR` in `librarian.py` or pass `--data-dir`):
   ```
   python librarian.py --build-index
   ```
4. **Start the archive:**
   ```
   python librarian.py
   ```
   It opens at http://127.0.0.1:8765. Click **Agent** for the AI librarian.

## The AI librarian

The agent page runs a local model through Ollama (default `qwen2.5:14b`; use
`--model qwen2.5:7b` for smaller GPUs). It starts Ollama if needed and offers to
download the model. Ask things like *"Give me some resources on black holes"*: it runs
several searches, reads articles, follows related links and returns a grouped reading
list with links checked against the archive.

## For other AI agents

- **HTTP API:** `http://127.0.0.1:8765/api/v1` (guide at `/agents.txt`, OpenAI-style
  tool schemas at `/api/v1/tools`)
- **MCP server:** `python librarian.py --mcp`, e.g. in `claude_desktop_config.json`:
  ```json
  {"mcpServers": {"offline-wikipedia": {"command": "python",
    "args": ["C:\\path\\to\\librarian.py", "--mcp"]}}}
  ```

The servers only accept requests from the local machine.

## Downloading responsibly

The downloader follows Wikimedia's guidance for dump downloads: at most 3 connections
(their per-IP cap), an identifying User-Agent, pauses between requests, back-off on
errors, and checksum verification. Please keep those settings.

## Tips

- On a hard drive, add the data folder to your antivirus exclusions; organizing writes
  millions of small files.
- The index builder reads the original compressed dump sequentially, which is much
  faster on hard drives than reading the organized files one by one.

## License of the content

Wikipedia text is licensed under [CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/).
If you redistribute content, credit Wikipedia and share adaptations under the same
license. This project is not affiliated with the Wikimedia Foundation.
