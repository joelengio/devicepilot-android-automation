# DevicePilot Architecture

## Control Plane

`device_controller.py` is the operator-facing control plane. It discovers emulator instances, stores UI/session state, chooses task sets, launches workers and aggregates status/log information.

## Automation Engine

`android_automation_engine.py` contains the device-facing execution layer:

- ADB transport and package operations
- BlueStacks discovery
- screenshot capture
- OpenCV image analysis
- OCR
- page-state recognition
- Android interaction primitives
- workflow and recovery logic
- optional external status synchronization

## Page Profiles

`pages.json` stores visual fingerprints used by the state detector. A profile may contain one or more screen regions, average RGB values and sampled pixel grids. These profiles allow state-aware automation instead of fixed-duration macro replay.

## Concurrency

The controller combines threading and multiprocessing depending on execution mode. Per-device state, logging and screenshot locks reduce cross-device interference.

## External Dependencies

ADB and BlueStacks are external system tools. OCR uses Tesseract and can optionally use EasyOCR. Google Sheets synchronization is optional and requires user-supplied credentials.
