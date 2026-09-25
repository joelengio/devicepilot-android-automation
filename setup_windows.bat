\
@echo off
setlocal
cd /d "%~dp0"

where python >nul 2>&1 || (
  echo Python was not found on PATH.
  exit /b 1
)

if not exist .venv (
  python -m venv .venv || exit /b 1
)

call .venv\Scripts\activate.bat
python -m pip install --upgrade pip
pip install -r requirements.txt

echo.
echo Core Python dependencies installed.
echo Ensure ADB is on PATH and configure .env before running the controller.
endlocal
