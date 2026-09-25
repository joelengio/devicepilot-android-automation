# Security

- Never commit Android application credentials, service-account files, tokens, APKs or private device logs.
- Keep `.env` local.
- Only connect to devices and applications you are authorized to test.
- Review logs before sharing; UI/OCR output can contain user-visible data.
- The project can issue ADB commands to configured devices. Use a dedicated emulator/test environment rather than a personal production device.
