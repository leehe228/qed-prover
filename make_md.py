#!/usr/bin/env python3
import os
import argparse
from pathlib import Path
from tqdm import tqdm
from datetime import datetime

def list_code_files_markdown(base_dir: str, extensions: tuple[str, ...], max_depth: int) -> str:
    base_path = Path(os.path.expanduser(base_dir)).resolve()
    if not base_path.is_dir():
        raise ValueError(f"Provided path is not a directory: {base_path}")
    
    base_depth = len(base_path.parts)
    output_lines = []

    for file_path in base_path.rglob('*'):
        if file_path.suffix not in extensions:
            continue
        current_depth = len(file_path.parts) - base_depth
        if current_depth > max_depth:
            continue

        try:
            code = file_path.read_text(encoding='utf-8')
        except Exception as e:
            output_lines.append(f'# Error reading {file_path}: {e}\n')
            continue

        relative_path = file_path.relative_to(base_path)
        
        # print
        print(f"- {relative_path}")
        
        lang = "python" if file_path.suffix == ".py" else "rust"
        output_lines.append(f'"""{relative_path}"""')
        output_lines.append(f"```{lang}")
        output_lines.append(code.rstrip())  # remove trailing newlines
        output_lines.append("```\n")

    return '\n'.join(output_lines)


def main():
    parser = argparse.ArgumentParser(description="Recursively extract code blocks from files and output as markdown.")
    parser.add_argument('--dir', type=str, required=True, help="Base directory to search")
    parser.add_argument('--ext', type=str, nargs='+', default=['.rs'], help="Extensions to include (e.g., .py .rs)")
    parser.add_argument('--depth', type=int, default=3, help="Max depth to recurse from base directory")
    parser.add_argument('--output', type=str, default="default", help="Output .txt file path")

    args = parser.parse_args()
    markdown_text = list_code_files_markdown(args.dir, tuple(args.ext), args.depth)

    if args.output == "default":
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        output_path = Path(f"./output_{timestamp}.txt").resolve()
    else:
        output_path = Path(os.path.expanduser(args.output)).resolve()

    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open('w', encoding='utf-8') as f:
        f.write(markdown_text)

    print(f"Done, file saved at {output_path}")

if __name__ == "__main__":
    main()
