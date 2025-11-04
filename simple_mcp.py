#!/usr/bin/env python3
"""
Simple MCP server without pydantic dependencies
Uses basic JSON-RPC over stdio
"""
import json
import sys
import os
from pathlib import Path


class SimpleMCP:
    def __init__(self, project_path):
        self.project_path = Path(project_path).resolve()
        self.tools = {
            "read_file": self.read_file,
            "list_files": self.list_files,
            "write_file": self.write_file
        }
    
    def read_file(self, path):
        """Read a file from the project directory"""
        try:
            file_path = self.project_path / path
            if not file_path.is_relative_to(self.project_path):
                return {"error": "Path outside project directory"}
            
            with open(file_path, 'r', encoding='utf-8') as f:
                return {"content": f.read()}
        except Exception as e:
            return {"error": str(e)}
    
    def list_files(self, path=""):
        """List files in a directory"""
        try:
            dir_path = self.project_path / path if path else self.project_path
            if not dir_path.is_relative_to(self.project_path):
                return {"error": "Path outside project directory"}
            
            files = []
            for item in dir_path.iterdir():
                files.append({
                    "name": item.name,
                    "type": "directory" if item.is_dir() else "file",
                    "path": str(item.relative_to(self.project_path))
                })
            return {"files": files}
        except Exception as e:
            return {"error": str(e)}
    
    def write_file(self, path, content):
        """Write content to a file"""
        try:
            file_path = self.project_path / path
            if not file_path.is_relative_to(self.project_path):
                return {"error": "Path outside project directory"}
            
            file_path.parent.mkdir(parents=True, exist_ok=True)
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(content)
            return {"success": True}
        except Exception as e:
            return {"error": str(e)}
    
    def handle_request(self, request):
        """Handle MCP request"""
        try:
            data = json.loads(request)
            method = data.get("method")
            params = data.get("params", {})
            id = data.get("id")
            
            if method == "initialize":
                return {
                    "jsonrpc": "2.0",
                    "id": id,
                    "result": {
                        "capabilities": {
                            "tools": list(self.tools.keys())
                        }
                    }
                }
            
            elif method == "tools/call":
                tool_name = params.get("name")
                tool_args = params.get("arguments", {})
                
                if tool_name in self.tools:
                    result = self.tools[tool_name](**tool_args)
                    return {
                        "jsonrpc": "2.0",
                        "id": id,
                        "result": {"content": [{"type": "text", "text": json.dumps(result)}]}
                    }
                else:
                    return {
                        "jsonrpc": "2.0",
                        "id": id,
                        "error": {"code": -32601, "message": f"Unknown tool: {tool_name}"}
                    }
            
            else:
                return {
                    "jsonrpc": "2.0",
                    "id": id,
                    "error": {"code": -32601, "message": f"Unknown method: {method}"}
                }
                
        except Exception as e:
            return {
                "jsonrpc": "2.0",
                "id": None,
                "error": {"code": -32603, "message": str(e)}
            }
    
    def run(self):
        """Run the MCP server"""
        for line in sys.stdin:
            line = line.strip()
            if line:
                response = self.handle_request(line)
                print(json.dumps(response))
                sys.stdout.flush()


if __name__ == "__main__":
    project_path = sys.argv[1] if len(sys.argv) > 1 else "."
    server = SimpleMCP(project_path)
    server.run()