# NESTOR VM — Student Instructions

Everything is installed on a shared server. You do not install anything on your computer. You connect to the server, run commands, and see results.

## Your credentials

- **Server address:** `20.86.154.197`
- **Your username:** `student1` (or student2, student3, student4, student5, student6 — Stergios will assign you one)
- **Password:** `nestor2026`

## Step 1: Open a terminal

### Windows
1. Press the **Windows key**, type `cmd`, press Enter. A black window opens.
2. That's your terminal.

If you have Windows 10 or later, `ssh` is already built in. If not, download PuTTY from https://putty.org — but try the built-in way first.

### Mac
1. Press **Cmd + Space**, type `Terminal`, press Enter.
2. That's your terminal.

### Linux
1. Press **Ctrl + Alt + T**.
2. That's your terminal.

## Step 2: Connect to the server

Type this in your terminal (replace `student1` with your assigned username):

```
ssh student1@20.86.154.197
```

It will ask:

```
Are you sure you want to continue connecting (yes/no)?
```

Type `yes` and press Enter.

Then it asks for your password. Type `nestor2026` and press Enter. **You will not see the password as you type — this is normal.** Just type it and press Enter.

You should see something like:

```
student1@nestor-vm:~$
```

That means you are on the server. Everything you type now runs on the server, not on your computer.

## Step 3: Run the demo

Type these three commands, one at a time:

```
cd ~/nestor
source .env
python3 demo.py
```

This runs 5 FraCaS items through the full NESTOR pipeline:
1. Shows you the English premise and hypothesis
2. An LLM (GPT-4o) translates them to first-order logic
3. Prover9 tries to prove the hypothesis from the premises
4. Mace4 tries to find a counterexample
5. The system gives a verdict: ENTAILMENT, CONTRADICTION, or NEUTRAL

Watch the output. Read the FOL translations. Read the proof traces. Understand what is happening at each step.

## Step 4: Run the existing test suite

After the demo, try the skill pipeline on the basic examples:

```
cd ~/nestor/skill_nli-fol-prover
python3 scripts/prove.py --file examples/basic.jsonl
```

This runs 8 test pairs. Look at the accuracy at the end.

## Step 5: Try your own example

```
cd ~/nestor/skill_nli-fol-prover
python3 scripts/prove.py -p "Every student is a person" -h "Some student is a person"
```

Try different premises and hypotheses. See what Prover9 can and cannot prove. Try:

- Changing "Every" to "Some" or "No"
- Multi-word predicates: "Every tall man is a man"
- Things that should be unknown: "John is a student" → "John is happy"

## Step 6: Read the briefing

```
cat ~/nestor/skill_nli-fol-prover/nestor_nesy_briefing.md
```

This explains what you need to build on top of the existing code.

## Common problems

**"Connection refused"** — The server might be turned off. Tell Stergios.

**"Permission denied"** — You typed the wrong password. Try again. Remember: `nestor2026`

**"command not found: python3"** — You forgot to `cd ~/nestor` first. The Python is system-wide so this shouldn't happen, but try: `/usr/bin/python3 demo.py`

**The demo crashes** — Copy the full error message and send it to the group chat.

**"No API key found"** — You forgot `source .env`. Run it again: `source /opt/nestor/.env`

## Disconnecting

Type `exit` or press **Ctrl + D** to disconnect. Your work is saved on the server. Next time, just `ssh` in again.

## Important

- **Do not delete files in /opt/nestor/** — everyone shares this folder.
- **Save your own work in your home folder:** `~/` (e.g., `~/my_experiments/`)
- **Do not change the .env file** — it has the API key everyone uses.
- **The API key costs money** — do not run thousands of items without asking Stergios first.
