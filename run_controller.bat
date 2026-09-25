\
@echo off
setlocal
cd /d "%~dp0"
if not exist .venv\Scripts\python.exe (
  echo Run setup_windows.bat first.
  exit /b 1
)
call .venv\Scripts\activate.bat
python device_controller.py
endlocal
